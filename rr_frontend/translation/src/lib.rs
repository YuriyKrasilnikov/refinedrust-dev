// © 2023, The RefinedRust Develcpers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

#![feature(box_patterns)]
#![feature(fn_traits)]
#![feature(rustc_private)]
#![feature(iter_order_by)]
#![feature(stmt_expr_attributes)]
#![feature(anonymous_lifetime_in_impl_trait)]
// This is useful to clearly state lifetimes of the global interners.
#![allow(clippy::needless_lifetimes)]
#![allow(clippy::elidable_lifetime_names)]

mod attrs;
mod base;
mod body;
mod closure_impl_generator;
mod consts;
mod environment;
mod error;
mod procedures;
mod regions;
mod rustcmp;
mod search;
mod shims;
mod spec_parsers;
mod traits;
mod types;
mod unification;

use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io::{Read as _, Write as _};
use std::path::{Path, PathBuf};
use std::{fs, io, process};

use log::{info, trace, warn};
use radium::{code, coq, lang, specs};
use rr_rustc_interface::borrowck::consumers::BodyWithBorrowckFacts;
use rr_rustc_interface::hir::def_id::{DefId, LocalDefId};
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::{hir, span};
use typed_arena::Arena;

use crate::base::OrderedDefId;
use crate::body::signature;
use crate::closure_impl_generator::ClosureImplGenerator;
use crate::environment::Environment;
use crate::shims::registry as shim_registry;
use crate::spec_parsers::const_attr_parser::{ConstAttrParser as _, VerboseConstAttrParser};
use crate::spec_parsers::crate_attr_parser::{CrateAttrParser as _, VerboseCrateAttrParser};
use crate::spec_parsers::module_attr_parser::{ModuleAttrParser as _, ModuleAttrs, VerboseModuleAttrParser};
use crate::traits::registry;
use crate::types::{normalize_in_function, scope};

pub struct VerificationCtxt<'tcx, 'rcx> {
    env: &'rcx Environment<'tcx>,
    procedure_registry: procedures::Scope<'tcx, 'rcx>,
    const_registry: consts::Scope<'rcx>,
    type_translator: &'rcx types::TX<'rcx, 'tcx>,
    trait_registry: &'rcx registry::TR<'tcx, 'rcx>,

    functions: &'rcx [LocalDefId],
    closures: &'rcx [LocalDefId],

    fn_arena: &'rcx Arena<specs::functions::Spec<'rcx, specs::functions::InnerSpec<'rcx>>>,

    /// the second component determines whether to include it in the code file as well
    extra_exports: BTreeSet<(coq::module::Export, bool)>,

    /// extra Coq module dependencies (for generated dune files)
    extra_dependencies: BTreeSet<coq::module::DirPath>,

    /// `RefinedRust` modules to export
    lib_exports: BTreeSet<String>,

    coq_path_prefix: String,
    dune_package: Option<String>,
    shim_registry: shims::registry::SR<'rcx>,

    /// trait implementations we generated
    trait_impls: BTreeMap<OrderedDefId, specs::traits::ImplSpec<'rcx>>,
    trait_impl_deps: BTreeMap<OrderedDefId, BTreeSet<OrderedDefId>>,
}

impl<'rcx> VerificationCtxt<'_, 'rcx> {
    fn get_path_for_shim(&self, did: DefId) -> (Vec<&str>, bool) {
        let path = shims::flat::get_export_path_for_did(self.env, did);
        let interned_path = self.shim_registry.intern_path(path.path.path);
        (interned_path, path.as_method)
    }

    fn make_shim_function_entry(&self, did: DefId) -> Option<shims::registry::FunctionShim<'_>> {
        let meta = self.procedure_registry.lookup_function(did)?;
        let mode = meta.get_mode();

        if mode != procedures::Mode::Prove
            && mode != procedures::Mode::OnlySpec
            && mode != procedures::Mode::TrustMe
            && mode != procedures::Mode::CodeShim
        {
            return None;
        }

        if self.env.tcx().visibility(did) != ty::Visibility::Public {
            // don't export
            return None;
        }

        // only export public items
        let (interned_path, as_method) = self.get_path_for_shim(did);
        let is_method = as_method;

        let name = base::strip_coq_ident(&self.env.get_item_name(did));
        info!("Found function path {:?} for did {:?} with name {:?}", interned_path, did, name);

        Some(shim_registry::FunctionShim {
            path: interned_path,
            is_method,
            name,
            trait_req_incl_name: meta.get_trait_req_incl_name().to_owned(),
            spec_name: meta.get_spec_name().to_owned(),
        })
    }

    /// Make a shim entry for a trait impl.
    fn make_trait_impl_shim_entry(
        &self,
        did: DefId,
        decl: &specs::traits::ImplSpec<'rcx>,
    ) -> Option<shim_registry::TraitImplShim> {
        info!("making shim entry for impl {did:?}");
        let impl_ref: ty::EarlyBinder<'_, ty::TraitRef<'_>> = self.env.tcx().impl_trait_ref(did);

        let impl_ref = normalize_in_function(did, self.env.tcx(), impl_ref.skip_binder()).unwrap();
        trace!("normalized impl_ref: {impl_ref:?}");

        let args = impl_ref.args;
        let trait_did = impl_ref.def_id;

        // the first arg is self, skip that
        // TODO don't handle Self specially, but treat it as any other arg
        let trait_args = &args.as_slice()[1..];
        let impl_for = args[0].expect_ty();

        // flatten the trait reference
        let trait_path = shims::flat::PathWithArgs::from_item(self.env, trait_did, trait_args)?;
        trace!("got trait path: {:?}", trait_path);

        // flatten the self type.
        let Some(for_type) = shims::flat::convert_ty_to_flat_type(self.env, impl_for) else {
            trace!("leave make_impl_shim_entry (failed transating self type)");
            return None;
        };

        trace!("implementation for: {:?}", impl_for);

        let mut method_specs = BTreeMap::new();
        for (name, spec) in &decl.methods.methods {
            if let specs::traits::InstanceMethodSpec::Defined(spec) = spec {
                method_specs.insert(
                    name.to_owned(),
                    (spec.function_name.clone(), spec.spec_name.clone(), spec.trait_req_incl_name.clone()),
                );
            }
            // otherwise (for default specs), we don't have to store anything, as this function
            // does not exist for Rust either
        }

        let a = shim_registry::TraitImplShim {
            trait_path,
            for_type,
            method_specs,
            specs: decl.trait_ref.impl_ref.clone(),
        };

        Some(a)
    }

    /// Make a shim entry for a trait.
    fn make_trait_shim_entry(
        &self,
        did: LocalDefId,
        decl: specs::traits::LiteralSpecRef<'rcx>,
    ) -> Option<shim_registry::TraitShim<'_>> {
        info!("making shim entry for {did:?}");
        if ty::Visibility::Public == self.env.tcx().visibility(did.to_def_id()) {
            let (interned_path, _) = self.get_path_for_shim(did.into());
            let a = shim_registry::TraitShim {
                path: interned_path,
                name: decl.name.clone(),
                has_semantic_interp: decl.has_semantic_interp,
                attrs_dependent: decl.attrs_dependent,
                allowed_attrs: decl.declared_attrs.clone(),
                method_trait_incl_decls: decl.method_trait_incl_decls.clone(),
            };
            return Some(a);
        }
        None
    }

    fn make_adt_shim_entry(
        &self,
        did: DefId,
        lit: specs::types::Literal,
    ) -> Option<shim_registry::AdtShim<'_>> {
        info!("making shim entry for {did:?}");
        if did.is_local() && ty::Visibility::Public == self.env.tcx().visibility(did) {
            // only export public items
            let (interned_path, _) = self.get_path_for_shim(did);
            let name = base::strip_coq_ident(&self.env.get_item_name(did));

            info!("Found adt path {:?} for did {:?} with name {:?}", interned_path, did, name);

            let a = shim_registry::AdtShim {
                path: interned_path,
                refinement_type: lit.refinement_type.to_string(),
                syn_type: lit.syn_type.to_string(),
                sem_type: lit.type_term,
                info: lit.info,
            };
            return Some(a);
        }

        None
    }

    fn generate_module_summary(&self, module_path: &str, module: &str, name: &str, path: &Path) {
        let mut function_shims = Vec::new();
        let mut adt_shims = Vec::new();
        let mut trait_shims = Vec::new();
        let mut trait_impl_shims = Vec::new();

        // traits
        let decls = self.trait_registry.get_trait_decls();
        for (did, decl) in &decls {
            if let Some(entry) = self.make_trait_shim_entry(did.def_id.expect_local(), decl.lit) {
                trait_shims.push(entry);
            }
        }

        // trait impls
        for (did, decl) in &self.trait_impls {
            if let Some(entry) = self.make_trait_impl_shim_entry(did.def_id, decl) {
                trait_impl_shims.push(entry);
            } else {
                info!("Creating trait impl shim entry failed for {did:?}");
            }
        }

        // ADTs
        let variant_defs = self.type_translator.get_variant_defs();
        let enum_defs = self.type_translator.get_enum_defs();

        for (did, entry) in &variant_defs {
            let entry = entry.borrow();
            if let Some(entry) = entry.as_ref()
                && let Some(shim) = self.make_adt_shim_entry(did.def_id, entry.make_literal_type())
            {
                adt_shims.push(shim);
            }
        }
        for (did, entry) in &enum_defs {
            let entry = entry.borrow();
            if let Some(entry) = entry.as_ref()
                && let Some(shim) = self.make_adt_shim_entry(did.def_id, entry.make_literal_type())
            {
                adt_shims.push(shim);
            }
        }

        // functions and methods
        for (did, _) in self.procedure_registry.iter_code() {
            if let Some(impl_did) = self.env.tcx().impl_of_assoc(did.def_id) {
                info!("found impl method: {:?}", did);
                if self.env.tcx().impl_is_of_trait(impl_did) {
                    info!("found trait method: {:?}", did);
                    continue;
                }
            }
            if let Some(shim) = self.make_shim_function_entry(did.def_id) {
                function_shims.push(shim);
            }
        }

        for (did, _) in self.procedure_registry.iter_only_spec() {
            if let Some(impl_did) = self.env.tcx().impl_of_assoc(did.def_id) {
                info!("found impl method: {:?}", did);
                if self.env.tcx().impl_is_of_trait(impl_did) {
                    info!("found trait method: {:?}", did);
                    continue;
                }
            }
            if let Some(shim) = self.make_shim_function_entry(did.def_id) {
                function_shims.push(shim);
            }
        }

        let mut module_dependencies: BTreeSet<coq::module::DirPath> =
            self.extra_exports.iter().filter_map(|(export, _)| export.get_path()).collect();

        module_dependencies.extend(self.extra_dependencies.iter().cloned());

        info!("Generated module summary ADTs: {:?}", adt_shims);
        info!("Generated module summary functions: {:?}", function_shims);

        let interface_file = File::create(path).unwrap();
        shims::registry::write_shims(
            interface_file,
            module_path,
            module,
            name,
            &module_dependencies,
            &self.lib_exports,
            adt_shims,
            function_shims,
            trait_shims,
            trait_impl_shims,
        );
    }

    /// Write specifications of a verification unit.
    fn write_specifications(&self, spec_path: &Path, code_path: &Path, stem: &str) {
        let common_imports = vec![
            coq::module::Import::new(vec!["lang", "notation"]).from(vec!["caesium"]),
            coq::module::Import::new(vec!["typing", "shims"]).from(vec!["refinedrust"]),
        ];

        let mut spec_file = io::BufWriter::new(File::create(spec_path).unwrap());
        let mut code_file = io::BufWriter::new(File::create(code_path).unwrap());

        {
            let mut spec_exports = Vec::new();
            spec_exports.append(&mut self.extra_exports.iter().map(|(export, _)| export.clone()).collect());
            spec_exports.push(
                coq::module::Export::new(vec![format!("generated_code_{stem}")])
                    .from(vec![&self.coq_path_prefix, stem]),
            );

            write!(spec_file, "{}", coq::module::ImportList(&common_imports)).unwrap();
            write!(spec_file, "{}", coq::module::ExportList(&spec_exports)).unwrap();
        }

        {
            let code_exports = self
                .extra_exports
                .iter()
                .filter(|(_, include)| *include)
                .map(|(export, _)| export.clone())
                .collect();

            write!(code_file, "{}", coq::module::ImportList(&common_imports)).unwrap();
            write!(code_file, "{}", coq::module::ExportList(&code_exports)).unwrap();
        }

        writeln!(spec_file).unwrap();

        // write trait attrs
        let trait_deps = self.trait_registry.get_registered_trait_deps();
        let dep_order = base::order_defs_with_deps(self.env.tcx(), &trait_deps);
        let trait_decls = self.trait_registry.get_trait_decls();

        for did in &dep_order {
            let ordered_did = OrderedDefId::new(self.env.tcx(), *did);
            let decl = &trait_decls[&ordered_did];
            write!(spec_file, "{}\n", decl.make_attr_record_decl()).unwrap();
        }

        // write semantic interps
        for did in &dep_order {
            let ordered_did = OrderedDefId::new(self.env.tcx(), *did);
            let decl = &trait_decls[&ordered_did];
            if let Some(decl) = decl.make_semantic_decl() {
                write!(spec_file, "{decl}\n").unwrap();
            }
        }

        // write structs, enums, and impl attrs
        // we need to do a bit of work to order them right
        {
            let struct_defs = self.type_translator.get_struct_defs();
            let enum_defs = self.type_translator.get_enum_defs();
            let mut adt_deps = self.type_translator.get_adt_deps();

            adt_deps.append(&mut self.trait_impl_deps.clone());

            let ordered = base::order_defs_with_deps(self.env.tcx(), &adt_deps);
            info!("ordered ADT defns: {:?}", ordered);

            for did in &ordered {
                let ordered_did = OrderedDefId::new(self.env.tcx(), *did);
                if let Some(su_ref) = struct_defs.get(&ordered_did) {
                    let su_ref = su_ref.borrow();
                    info!("writing struct {:?}, {:?}", did, su_ref);
                    let su = su_ref.as_ref().unwrap();

                    // layout specs
                    writeln!(code_file, "{}", su.generate_coq_sls_def()).unwrap();

                    // type aliases
                    writeln!(spec_file, "{}", su.generate_coq_type_def()).unwrap();
                } else if let Some(eu_ref) = enum_defs.get(&ordered_did) {
                    let eu = eu_ref.borrow();
                    let eu = eu.as_ref().unwrap();
                    info!("writing enum {:?}, {:?}", did, eu);

                    // layout specs
                    writeln!(code_file, "{}", eu.generate_coq_els_def()).unwrap();

                    // type definition
                    writeln!(spec_file, "{}", eu.generate_coq_type_def()).unwrap();
                } else if let Some(impl_ref) = self.trait_impls.get(&ordered_did) {
                    writeln!(spec_file, "Section attrs.").unwrap();
                    writeln!(spec_file, "Context `{{RRGS : !refinedrustGS Σ}}.").unwrap();
                    writeln!(spec_file, "{}\n", impl_ref.generate_attr_decl()).unwrap();
                    writeln!(spec_file, "End attrs.\n").unwrap();
                }
            }
        }

        // write tuples up to the necessary size
        // TODO

        // write the attribute spec declarations of closure trait impls
        {
            writeln!(spec_file, "Section closure_attrs.").unwrap();
            writeln!(spec_file, "Context `{{RRGS : !refinedrustGS Σ}}.").unwrap();
            for info in self.procedure_registry.closure_info.values() {
                for spec in &info.generated_impls {
                    writeln!(spec_file, "{}\n", spec.generate_attr_decl()).unwrap();
                }
            }
            writeln!(spec_file, "End closure_attrs.\n").unwrap();
        }

        // Include extra specs
        {
            if let Some(extra_specs_path) = rrconfig::extra_specs_file() {
                writeln!(
                    spec_file,
                    "(* Included specifications from configured file {} *)",
                    extra_specs_path.display()
                )
                .unwrap();

                let mut extra_specs_file = io::BufReader::new(File::open(extra_specs_path).unwrap());
                let mut extra_specs_string = String::new();
                extra_specs_file.read_to_string(&mut extra_specs_string).unwrap();

                write!(spec_file, "{}", extra_specs_string).unwrap();
            }
        }

        // write trait specs
        for did in &dep_order {
            let ordered_did = OrderedDefId::new(self.env.tcx(), *did);
            let decl = &trait_decls[&ordered_did];
            write!(spec_file, "{}\n", decl.make_spec_record_decl()).unwrap();
        }

        // write remaining trait things
        for did in &dep_order {
            let ordered_did = OrderedDefId::new(self.env.tcx(), *did);
            let decl = &trait_decls[&ordered_did];
            write!(spec_file, "{decl}\n").unwrap();
        }

        // write trait req incls
        for did in &dep_order {
            let ordered_did = OrderedDefId::new(self.env.tcx(), *did);
            let decl = &trait_decls[&ordered_did];
            write!(spec_file, "{}\n", decl.make_trait_req_incls()).unwrap();
        }

        {
            // write translated source code of functions
            writeln!(code_file, "Section code.").unwrap();
            writeln!(code_file, "Context `{{RRGS : !refinedrustGS Σ}}.").unwrap();
            writeln!(code_file, "Open Scope printing_sugar.").unwrap();
            writeln!(code_file).unwrap();

            let mut ordered_by_name = BTreeMap::new();
            for (did, fun) in self.procedure_registry.iter_code() {
                if self.procedure_registry.lookup_function_mode(did.def_id).unwrap().needs_def() {
                    ordered_by_name.insert(fun.name().to_owned(), fun);
                }
            }
            for fun in ordered_by_name.values() {
                writeln!(code_file, "{}", fun.code).unwrap();
                writeln!(code_file).unwrap();
            }

            // generate the code for closure trait shims
            writeln!(code_file, "(* closure shims *)").unwrap();
            for info in self.procedure_registry.closure_info.values() {
                for def in &info.generated_functions {
                    writeln!(code_file, "{}", def.code).unwrap();
                    writeln!(code_file).unwrap();
                }
            }
            write!(code_file, "End code.").unwrap();
        }

        // write function specs
        {
            writeln!(spec_file, "Section specs.").unwrap();
            writeln!(spec_file, "Context `{{RRGS : !refinedrustGS Σ}}.").unwrap();
            writeln!(spec_file).unwrap();

            for (did, fun) in self.procedure_registry.iter_code() {
                let meta = self.procedure_registry.lookup_function(did.def_id).unwrap();
                if !meta.is_trait_default() {
                    if fun.spec.is_complete() {
                        //if fun.spec.spec.args.len() != fun.code.get_argument_count() {
                        //warn!("Function specification for {} is missing arguments", fun.name());
                        //}
                        writeln!(spec_file, "{}", fun.spec.generate_trait_req_incl_def()).unwrap();
                        writeln!(spec_file, "{}", fun.spec).unwrap();
                    } else {
                        warn!("No specification for {}", fun.name());

                        writeln!(spec_file, "(* No specification provided for {} *)", fun.name()).unwrap();
                    }
                }
            }
            writeln!(spec_file).unwrap();
        }

        // also write only-spec functions specs
        {
            for (did, spec) in self.procedure_registry.iter_only_spec() {
                let meta = self.procedure_registry.lookup_function(did.def_id).unwrap();
                if !meta.is_trait_default() {
                    if spec.is_complete() {
                        writeln!(spec_file, "{}", spec.generate_trait_req_incl_def()).unwrap();
                        writeln!(spec_file, "{spec}").unwrap();
                    } else {
                        writeln!(spec_file, "(* No specification provided for {} *)", spec.function_name)
                            .unwrap();
                    }
                }
            }
            writeln!(spec_file).unwrap();
        }

        // write specs for closure trait impls
        {
            for info in self.procedure_registry.closure_info.values() {
                for def in &info.generated_functions {
                    writeln!(spec_file, "{}", def.spec.generate_trait_req_incl_def()).unwrap();
                    writeln!(spec_file, "{}", def.spec).unwrap();
                }
            }
            writeln!(spec_file).unwrap();
        }

        writeln!(spec_file, "End specs.").unwrap();

        // write trait impls
        {
            for spec in self.trait_impls.values() {
                writeln!(spec_file, "{spec}").unwrap();
            }
        }

        // write closure trait impls
        {
            for info in self.procedure_registry.closure_info.values() {
                for spec in &info.generated_impls {
                    writeln!(spec_file, "{spec}").unwrap();
                }
            }
        }
    }

    /// Write proof templates for a verification unit.
    fn write_templates<F>(&self, file_path: F, stem: &str)
    where
        F: Fn(&str) -> PathBuf,
    {
        let common_imports = vec![
            coq::module::Import::new(vec!["lang", "notation"]).from(vec!["caesium"]),
            coq::module::Import::new(vec!["typing", "shims"]).from(vec!["refinedrust"]),
        ];

        // This closure does the core part of writing the template
        let write_template = |file: &mut io::BufWriter<File>,
                              fun: &code::Function<'_>,
                              is_trait_default: bool| {
            let imports = common_imports.clone();

            let mut exports: Vec<_> = self.extra_exports.iter().map(|(export, _)| export.clone()).collect();
            exports.push(
                coq::module::Export::new(vec![
                    &format!("generated_code_{stem}"),
                    &format!("generated_specs_{stem}"),
                ])
                .from(vec![&self.coq_path_prefix, stem]),
            );

            write!(file, "{}", coq::module::ImportList(&imports)).unwrap();
            write!(file, "{}", coq::module::ExportList(&exports)).unwrap();
            write!(file, "\n").unwrap();

            write!(file, "Set Default Proof Using \"Type\".\n\n").unwrap();
            write!(
                file,
                "\
                Section proof.\n\
                Context `{{RRGS : !refinedrustGS Σ}}.\n"
            )
            .unwrap();

            fun.generate_lemma_statement(file, is_trait_default).unwrap();

            write!(file, "End proof.\n\n").unwrap();

            fun.generate_proof_prelude(file, is_trait_default).unwrap();
        };

        // write templates
        // each function gets a separate file in order to parallelize
        for (did, fun) in self.procedure_registry.iter_code() {
            let path = file_path(fun.name());
            let mut template_file = io::BufWriter::new(File::create(path.as_path()).unwrap());

            let meta = self.procedure_registry.lookup_function(did.def_id).unwrap();
            let mode = meta.get_mode();

            if fun.spec.is_complete() && mode.needs_proof() {
                write_template(&mut template_file, fun, meta.is_trait_default());
            } else if !fun.spec.is_complete() {
                write!(template_file, "(* No specification provided *)").unwrap();
            } else {
                write!(template_file, "(* Function is trusted *)").unwrap();
            }
        }

        // also write templates for the closure shim proofs
        {
            for info in self.procedure_registry.closure_info.values() {
                for fun in &info.generated_functions {
                    let path = file_path(fun.name());
                    let mut template_file = io::BufWriter::new(File::create(path.as_path()).unwrap());
                    write_template(&mut template_file, fun, false);
                }
            }
        }
    }

    fn check_function_needs_proof(&self, did: DefId, fun: &code::Function<'_>) -> bool {
        let mode = self.procedure_registry.lookup_function_mode(did).unwrap();
        fun.spec.is_complete() && mode.needs_proof()
    }

    /// Write proofs for a verification unit.
    fn write_proofs<F, G>(
        &self,
        proof_dir_path: &Path,
        file_path: F,
        trait_file_path: G,
        stem: &str,
    ) -> Vec<String>
    where
        F: Fn(&str) -> String,
        G: Fn(&str) -> String,
    {
        let common_imports = vec![
            coq::module::Import::new(vec!["lang", "notation"]).from(vec!["caesium"]),
            coq::module::Import::new(vec!["typing", "shims"]).from(vec!["refinedrust"]),
        ];

        let mut proof_modules = Vec::new();

        // write proofs
        // each function gets a separate file in order to parallelize
        let mut write_proof = |fun: &code::Function<'_>| {
            let module_path = file_path(fun.name());
            let path = proof_dir_path.join(format!("{module_path}.v"));

            proof_modules.push(module_path);

            if path.exists() {
                info!("Proof file for function {} already exists, skipping creation", fun.name());
                return;
            }

            info!("Proof file for function {} does not yet exist, creating", fun.name());

            let mut proof_file = io::BufWriter::new(File::create(path.as_path()).unwrap());

            let mut imports = common_imports.clone();

            imports.append(&mut vec![
                coq::module::Import::new(vec![
                    &format!("generated_code_{stem}"),
                    &format!("generated_specs_{stem}"),
                    &format!("generated_template_{}", fun.name()),
                ])
                .from(vec![&self.coq_path_prefix, stem, "generated"]),
            ]);

            writeln!(proof_file, "{}", coq::module::ImportList(&imports)).unwrap();

            // Note: we do not export the self.extra_exports explicitly, as we rely on them
            // being re-exported from the template -- we want to be stable under changes of the
            // extras

            writeln!(proof_file, "Set Default Proof Using \"Type\".").unwrap();
            writeln!(proof_file).unwrap();

            writeln!(proof_file, "Section proof.").unwrap();
            writeln!(proof_file, "Context `{{RRGS : !refinedrustGS Σ}}.").unwrap();
            writeln!(proof_file).unwrap();

            fun.generate_proof(&mut proof_file, rrconfig::admit_proofs()).unwrap();

            writeln!(proof_file, "End proof.").unwrap();
        };

        for (did, fun) in self.procedure_registry.iter_code() {
            if !self.check_function_needs_proof(did.def_id, fun) {
                continue;
            }
            write_proof(fun);
        }

        // also write proofs for closure shims
        for info in self.procedure_registry.closure_info.values() {
            for fun in &info.generated_functions {
                write_proof(fun);
            }
        }

        let mut write_trait_incl = |spec: &specs::traits::ImplSpec<'_>| {
            let name = &spec.trait_ref.impl_ref.spec_subsumption_proof();
            let module_path = trait_file_path(name.as_str());
            let path = proof_dir_path.join(format!("{module_path}.v"));

            proof_modules.push(module_path);

            if path.exists() {
                info!("Proof file for trait impl {} already exists, skipping creation", name);
                return;
            }

            info!("Proof file for trait impl {} does not yet exist, creating", name);

            let mut proof_file = io::BufWriter::new(File::create(path.as_path()).unwrap());

            let mut imports = common_imports.clone();

            imports.append(&mut vec![
                coq::module::Import::new(vec![&format!("generated_specs_{stem}")]).from(vec![
                    &self.coq_path_prefix,
                    stem,
                    "generated",
                ]),
            ]);

            writeln!(proof_file, "{}", coq::module::ImportList(&imports)).unwrap();

            // Note: we do not export the self.extra_exports explicitly, as we rely on them
            // being re-exported from the template -- we want to be stable under changes of the
            // extras

            writeln!(proof_file, "Set Default Proof Using \"Type\".").unwrap();
            writeln!(proof_file).unwrap();

            writeln!(proof_file, "Section proof.").unwrap();
            writeln!(proof_file, "Context `{{RRGS : !refinedrustGS Σ}}.").unwrap();
            writeln!(proof_file).unwrap();

            write!(proof_file, "{}", spec.generate_proof()).unwrap();

            writeln!(proof_file, "End proof.").unwrap();
        };

        // write file for trait incls
        for spec in self.trait_impls.values() {
            write_trait_incl(spec);
        }

        // also for closure shims
        for info in self.procedure_registry.closure_info.values() {
            for spec in &info.generated_impls {
                write_trait_incl(spec);
            }
        }

        proof_modules
    }

    /// Write Coq files for this verification unit.
    pub fn write_coq_files(&self) {
        // use the crate_name for naming
        let crate_name: span::symbol::Symbol = self.env.tcx().crate_name(span::def_id::LOCAL_CRATE);
        let stem = crate_name.as_str();

        // create output directory
        let Some(mut base_dir_path) = rrconfig::output_dir() else {
            info!("No output directory specified, not writing files");
            return;
        };

        base_dir_path.push(stem);

        if fs::read_dir(base_dir_path.as_path()).is_err() {
            warn!("Output directory {:?} does not exist, creating directory", base_dir_path.display());
            fs::create_dir_all(base_dir_path.as_path()).unwrap();
        }

        let toplevel_module_path = self.coq_path_prefix.clone();
        let coq_module_path = format!("{}.{}", toplevel_module_path, stem);
        let generated_module_path = format!("{}.generated", coq_module_path);
        let proof_module_path = format!("{}.proofs", coq_module_path);

        // write gitignore file
        let gitignore_path = base_dir_path.as_path().join(".gitignore");
        {
            if !gitignore_path.as_path().exists() {
                let mut gitignore_file = io::BufWriter::new(File::create(gitignore_path.as_path()).unwrap());
                write!(
                    gitignore_file,
                    "\
                    generated\n\
                    proofs/dune\n\
                    interface.rrlib"
                )
                .unwrap();
            }
        }

        // build the path for generated files
        base_dir_path.push("generated");
        let generated_dir_path = base_dir_path.clone();
        let generated_dir_path = generated_dir_path.as_path();

        // build the path for proof files
        base_dir_path.pop();
        base_dir_path.push("proofs");
        let proof_dir_path = base_dir_path.clone();
        let proof_dir_path = proof_dir_path.as_path();

        // build the path for the interface file
        base_dir_path.pop();
        base_dir_path.push("interface.rrlib");
        self.generate_module_summary(
            &generated_module_path,
            &format!("generated_specs_{}", stem),
            stem,
            base_dir_path.as_path(),
        );

        // write the dune-project file, if required
        if rrconfig::generate_dune_project() {
            base_dir_path.pop();
            base_dir_path.pop();
            base_dir_path.push("dune-project");

            let dune_project_path = base_dir_path.as_path();

            if !dune_project_path.exists() {
                let mut dune_project_file = io::BufWriter::new(File::create(dune_project_path).unwrap());

                let (project_name, dune_project_package) = if let Some(dune_package) = &self.dune_package {
                    (dune_package.to_owned(), format!("(package (name {dune_package}))\n"))
                } else {
                    (stem.to_owned(), String::new())
                };

                write!(
                    dune_project_file,
                    "\
                    (lang dune 3.21)\n\
                    (using rocq 0.11)\n\
                    (name {project_name})\n{dune_project_package}",
                )
                .unwrap();
            }
        }

        // write generated (subdirectory "generated")
        info!("outputting generated code to {}", generated_dir_path.to_str().unwrap());
        if fs::read_dir(generated_dir_path).is_err() {
            warn!("Output directory {} does not exist, creating directory", generated_dir_path.display());
        } else {
            // purge contents
            info!("Removing the contents of the generated directory");
            fs::remove_dir_all(generated_dir_path).unwrap();
        }
        fs::create_dir_all(generated_dir_path).unwrap();

        let code_path = generated_dir_path.join(format!("generated_code_{}.v", stem));
        let spec_path = generated_dir_path.join(format!("generated_specs_{}.v", stem));
        let generated_dune_path = generated_dir_path.join("dune");

        // write specs
        self.write_specifications(spec_path.as_path(), code_path.as_path(), stem);

        // write templates
        self.write_templates(|name| generated_dir_path.join(format!("generated_template_{name}.v")), stem);

        // write dune meta file
        let mut dune_file = io::BufWriter::new(File::create(generated_dune_path.as_path()).unwrap());

        let mut extra_theories: BTreeSet<coq::module::DirPath> =
            self.extra_exports.iter().filter_map(|(export, _)| export.get_path()).collect();

        extra_theories.extend(self.extra_dependencies.iter().cloned());

        let extra_theories: Vec<String> = extra_theories.into_iter().map(|x| x.to_string()).collect();

        let dune_package = if let Some(dune_package) = &self.dune_package {
            format!("(package {dune_package})\n")
        } else {
            String::new()
        };

        write!(
            dune_file,
            "\
            ; Generated by [refinedrust], do not edit.\n\
            (rocq.theory\n\
             (flags -w -notation-overridden -w -redundant-canonical-projection)\n{dune_package}\
             (name {generated_module_path})\n\
             (generate_project_file)\n\
             (theories stdpp iris iris_contrib Ltac2 Equations lrust caesium lithium refinedrust Stdlib {}))",
            extra_theories.join(" ")
        )
        .unwrap();

        // write proofs (subdirectory "proofs")
        let make_proof_file_name = |name| format!("proof_{}.v", name);

        info!("using {} as proof directory", proof_dir_path.to_str().unwrap());
        if let Ok(read) = fs::read_dir(proof_dir_path) {
            // directory already exists, we want to check if there are any stale proof files and
            // issue a warning in that case

            // build the set of proof files we are going to expect
            let mut proof_files_to_generate = BTreeSet::new();
            for (did, fun) in self.procedure_registry.iter_code() {
                if self.check_function_needs_proof(did.def_id, fun) {
                    proof_files_to_generate.insert(make_proof_file_name(fun.name()));
                }
            }

            for file in read.flatten() {
                // check if the file name is okay
                let filename = file.file_name();
                let Some(filename) = filename.to_str() else {
                    continue;
                };

                if filename == "dune" {
                    continue;
                }
                if proof_files_to_generate.contains(filename) {
                    continue;
                }

                println!("Warning: Proof file {filename} does not have a matching Rust function to verify.");
            }
        } else {
            warn!("Output directory {} does not exist, creating directory", proof_dir_path.display());
            fs::create_dir_all(proof_dir_path).unwrap();
        }

        // explicitly spell out the proof modules we want to compile so we don't choke on stale
        // proof files
        let proof_modules = self.write_proofs(
            proof_dir_path,
            |name| format!("proof_{name}"),
            |name| format!("trait_incl_{name}"),
            stem,
        );

        // write proof dune file
        let proof_dune_path = proof_dir_path.join("dune");
        let mut dune_file = io::BufWriter::new(File::create(proof_dune_path.as_path()).unwrap());
        write!(dune_file, "\
            ; Generated by [refinedrust], do not edit.\n\
            (rocq.theory\n\
             (flags -w -notation-overridden -w -redundant-canonical-projection)\n{dune_package}\
             (name {proof_module_path})\n\
             (modules {})\n\
             (generate_project_file)\n\
             (theories stdpp iris Ltac2 Equations lrust caesium lithium refinedrust Stdlib {} {}.{}.generated))",
             proof_modules.join(" "), extra_theories.join(" "), self.coq_path_prefix, stem).unwrap();
    }
}

fn resolve_shim(vcx: &VerificationCtxt<'_, '_>, path: &[&str], is_method: bool) -> Option<DefId> {
    if is_method {
        search::try_resolve_method_did(vcx.env.tcx(), path.iter().map(ToString::to_string).collect())
    } else {
        search::try_resolve_did(vcx.env.tcx(), path)
    }
}

/// Register shims in the procedure registry.
fn register_shims<'tcx>(vcx: &mut VerificationCtxt<'tcx, '_>) -> Result<(), base::TranslationError<'tcx>> {
    for shim in vcx.shim_registry.get_function_shims() {
        let did = resolve_shim(vcx, &shim.path, shim.is_method);

        match did {
            Some(did) => {
                // register as usual in the procedure registry
                info!("registering shim for {:?}", shim.path);
                let meta = procedures::Meta::new(
                    shim.spec_name.clone(),
                    "dummy".to_owned(),
                    shim.trait_req_incl_name.clone(),
                    shim.name.clone(),
                    procedures::Mode::Shim,
                    false,
                    false,
                );
                vcx.procedure_registry.register_function(did, meta)?;
            },
            _ => {
                println!("Warning: cannot find defid for shim {:?}, skipping", shim.path);
            },
        }
    }

    for shim in vcx.shim_registry.get_adt_shims() {
        let Some(did) = search::try_resolve_did(vcx.env.tcx(), &shim.path) else {
            println!("Warning: cannot find defid for shim {:?}, skipping", shim.path);
            continue;
        };

        let lit = specs::types::Literal {
            rust_name: None,
            type_term: shim.sem_type.clone(),
            syn_type: lang::SynType::Literal(shim.syn_type.clone()),
            refinement_type: coq::term::Type::Literal(shim.refinement_type.clone()),
            info: shim.info.clone(),
        };

        if let Err(e) = vcx.type_translator.register_adt_shim(did, &lit) {
            println!("Warning: {}", e);
        }

        info!("Resolved ADT shim {:?} as {:?} did", shim, did);
    }

    for shim in vcx.shim_registry.get_trait_shims() {
        if let Some(did) = search::try_resolve_did(vcx.env.tcx(), &shim.path) {
            let assoc_tys = vcx.trait_registry.get_associated_type_names(did);
            let spec = specs::traits::LiteralSpec {
                assoc_tys,
                name: shim.name.clone(),
                has_semantic_interp: shim.has_semantic_interp,
                attrs_dependent: shim.attrs_dependent,
                declared_attrs: shim.allowed_attrs.clone(),
                method_trait_incl_decls: shim.method_trait_incl_decls.clone(),
            };

            vcx.trait_registry.register_shim(did, spec)?;
        } else {
            println!("Warning: cannot find defid for shim {:?}, skipping", shim.path);
        }
    }

    for shim in vcx.shim_registry.get_trait_impl_shims() {
        // resolve the trait
        let Some((trait_did, args)) = shim.trait_path.to_item(vcx.env.tcx()) else {
            println!("Warning: cannot resolve {:?} as a trait, skipping shim", shim.trait_path);
            continue;
        };

        if !vcx.env.tcx().is_trait(trait_did) {
            println!("Warning: This is not a trait: {:?}", shim.trait_path);
            continue;
        }

        // resolve the type
        let Some(for_type) = shim.for_type.to_type(vcx.env.tcx()) else {
            println!("Warning: cannot resolve {:?} as a type, skipping shim", shim.for_type);
            continue;
        };

        let trait_impl_did = search::try_resolve_trait_impl_did(vcx.env.tcx(), trait_did, &args, for_type);

        let Some(did) = trait_impl_did else {
            println!(
                "Warning: cannot find defid for implementation of {:?} for {:?}",
                shim.trait_path, for_type
            );
            continue;
        };

        vcx.trait_registry.register_impl_shim(did, shim.specs.clone())?;

        // now register all the method shims
        let impl_assoc_items: &ty::AssocItems = vcx.env.tcx().associated_items(did);
        for (method_name, (name, spec_name, trait_req_incl_name)) in &shim.method_specs {
            // find the right item
            if let Some(item) = impl_assoc_items.find_by_ident_and_kind(
                vcx.env.tcx(),
                span::symbol::Ident::from_str(method_name),
                ty::AssocTag::Fn,
                trait_did,
            ) {
                let method_did = item.def_id;
                // register as usual in the procedure registry
                info!(
                    "registering shim for implementation of {:?}::{:?} for {:?}, using method {:?}",
                    shim.trait_path, method_name, for_type, method_did
                );

                let meta = procedures::Meta::new(
                    spec_name.clone(),
                    "dummy".to_owned(),
                    trait_req_incl_name.clone(),
                    name.clone(),
                    procedures::Mode::Shim,
                    false,
                    false,
                );

                vcx.procedure_registry.register_function(method_did, meta)?;
            }
        }
    }

    // add the extra exports
    vcx.extra_exports
        .extend(vcx.shim_registry.get_extra_exports().iter().map(|export| (export.clone(), true)));
    // add the extra dependencies
    vcx.extra_dependencies.extend(vcx.shim_registry.get_extra_dependencies().iter().cloned());

    Ok(())
}

/// Check if this is a function whose implementation we always skip, asserting just a
/// specification.
/// This is unsafe, and should only be done for functions we really don't care about.
fn is_only_spec_function(vcx: &VerificationCtxt<'_, '_>, did: DefId) -> bool {
    // Check if `did` is an impl of `Debug::fmt`. These impls use unsupported features like strings
    // and trait objects, but don't do anything functionally interesting.

    if let Some(impl_did) = vcx.env.trait_impl_of_method(did) {
        let subject = vcx.env.tcx().impl_trait_header(impl_did);
        let trait_ref = subject.trait_ref.skip_binder();
        let debug_did = search::try_resolve_did(vcx.env.tcx(), &["core", "fmt", "Debug"]);
        if rrconfig::trust_debug() && debug_did == Some(trait_ref.def_id) {
            println!("Warning: automatically trusting implementation of `Debug::fmt`: {did:?}");
            return true;
        }
    }

    false
}

/// Get the most restrictive function mode arising from annotations on a function.
fn get_most_restrictive_function_mode(vcx: &VerificationCtxt<'_, '_>, did: DefId) -> procedures::Mode {
    let attrs = vcx.env.get_attributes_of_function(did, &spec_parsers::propagate_method_attr_from_impl);

    // check if this is a purely spec function; if so, skip.
    if attrs::has_tool_attr_filtered(attrs.as_slice(), "shim") {
        return procedures::Mode::Shim;
    }

    if attrs::has_tool_attr_filtered(attrs.as_slice(), "trust_me") {
        return procedures::Mode::TrustMe;
    }

    if attrs::has_tool_attr_filtered(attrs.as_slice(), "code_shim") {
        return procedures::Mode::CodeShim;
    }

    if attrs::has_tool_attr_filtered(attrs.as_slice(), "only_spec") || is_only_spec_function(vcx, did) {
        return procedures::Mode::OnlySpec;
    }

    if attrs::has_tool_attr_filtered(attrs.as_slice(), "ignore") {
        info!("Function {:?} will be ignored", did);
        return procedures::Mode::Ignore;
    }

    procedures::Mode::Prove
}

/// Register functions of the crate in the procedure registry.
fn register_functions<'tcx>(
    vcx: &mut VerificationCtxt<'tcx, '_>,
) -> Result<(), base::TranslationError<'tcx>> {
    for (f, is_closure) in vcx
        .functions
        .iter()
        .map(|did| (did, false))
        .chain(vcx.closures.iter().map(|did| (did, true)))
    {
        if !check_consider_function(&*vcx, *f)? {
            continue;
        }

        let mut mode = get_most_restrictive_function_mode(vcx, f.to_def_id());

        let fname = base::strip_coq_ident(&vcx.env.get_item_name(f.to_def_id()));
        //let fname = format!("{stem}_{fname}");
        let spec_name = format!("type_of_{}", fname);
        let code_name = format!("{}_def", fname);
        let trait_req_incl_name = format!("trait_incl_of_{}", fname);

        // check whether this is part of a trait decl
        let is_default_trait_impl = vcx.env.tcx().trait_of_assoc(f.to_def_id()).is_some();

        if mode == procedures::Mode::Shim && is_default_trait_impl {
            warn!("ignoring rr::shim attribute on default trait impl");
            mode = procedures::Mode::Prove;
        }
        if mode == procedures::Mode::Shim {
            // TODO better error message
            let attrs = vcx.env.get_attributes(f.to_def_id());
            let v = attrs::filter_for_tool(attrs);
            let annot = spec_parsers::get_shim_attrs(v.as_slice()).unwrap();

            info!(
                "Registering shim: {:?} as spec: {}, code: {}",
                f.to_def_id(),
                annot.spec_name,
                annot.code_name
            );
            let meta = procedures::Meta::new(
                annot.spec_name,
                annot.code_name,
                annot.trait_req_incl_name,
                fname.clone(),
                procedures::Mode::Shim,
                is_default_trait_impl,
                is_closure,
            );
            vcx.procedure_registry.register_function(f.to_def_id(), meta)?;

            continue;
        }
        if mode == procedures::Mode::CodeShim {
            // TODO better error message
            let attrs = vcx.env.get_attributes(f.to_def_id());
            let v = attrs::filter_for_tool(attrs);
            let annot = spec_parsers::get_code_shim_attrs(v.as_slice()).unwrap();

            info!("Registering code shim: {:?} as {}", f.to_def_id(), annot.code_name);
            let meta = procedures::Meta::new(
                spec_name,
                annot.code_name,
                trait_req_incl_name,
                fname.clone(),
                procedures::Mode::CodeShim,
                is_default_trait_impl,
                is_closure,
            );
            vcx.procedure_registry.register_function(f.to_def_id(), meta)?;

            continue;
        }

        if mode == procedures::Mode::Prove
            && let Some(impl_did) = vcx.env.tcx().impl_of_assoc(f.to_def_id())
        {
            mode = get_most_restrictive_function_mode(vcx, impl_did);
        }

        if mode.is_shim() || mode.is_code_shim() {
            warn!("Nonsensical shim attribute on impl; ignoring");
            mode = procedures::Mode::Prove;
        }

        // also register it under the export path, if annotated.
        if let Some(export_path) = shims::flat::get_external_export_path_for_did(vcx.env, f.to_def_id()) {
            let interned_path = vcx.shim_registry.intern_path(export_path.path.path);
            info!("Looking up annotated shim {interned_path:?} for is_method={:?}", export_path.as_method);
            if let Some(export_did) = resolve_shim(vcx, &interned_path, export_path.as_method) {
                let meta = procedures::Meta::new(
                    spec_name.clone(),
                    code_name.clone(),
                    trait_req_incl_name.clone(),
                    fname.clone(),
                    procedures::Mode::Shim,
                    is_default_trait_impl,
                    is_closure,
                );
                vcx.procedure_registry.register_function(export_did, meta)?;
            } else {
                warn!("Could not resolve annotated export path {interned_path:?}");
            }
        }

        //info!("Registering function {f:?} with is_default_trait_impl={is_default_trait_impl}");
        let meta = procedures::Meta::new(
            spec_name,
            code_name,
            trait_req_incl_name,
            fname,
            mode,
            is_default_trait_impl,
            is_closure,
        );

        vcx.procedure_registry.register_function(f.to_def_id(), meta)?;
    }

    Ok(())
}

/// Translate functions of the crate, assuming they were previously registered.
fn translate_functions(vcx: &mut VerificationCtxt<'_, '_>) {
    // First translate closures, then functions: the function translation assumes that closures
    // they contain have been translated already.
    for &f in vcx.closures.iter().chain(vcx.functions.iter()) {
        if vcx.procedure_registry.lookup_function(f.to_def_id()).is_some() && !translate_function(vcx, f) {
            break;
        }
    }
}

fn translate_function<'tcx>(vcx: &mut VerificationCtxt<'tcx, '_>, f: LocalDefId) -> bool {
    let proc = vcx.env.get_procedure(f.to_def_id());
    let fname = vcx.env.get_item_name(f.to_def_id());
    let meta = vcx.procedure_registry.lookup_function(f.to_def_id()).unwrap();

    let filtered_attrs = vcx
        .env
        .get_attributes_of_function(f.to_def_id(), &spec_parsers::propagate_method_attr_from_impl);

    let mode = meta.get_mode();
    if mode.is_shim() {
        return true;
    }
    if mode.is_ignore() {
        return true;
    }

    info!("\nTranslating function {}", fname);

    let ty: ty::EarlyBinder<'_, ty::Ty<'tcx>> = vcx.env.tcx().type_of(proc.get_id());
    let ty = ty.instantiate_identity();

    let translator = match ty.kind() {
        ty::TyKind::FnDef(_def, _args) => signature::TX::new(
            vcx.env,
            &meta,
            proc,
            &filtered_attrs,
            vcx.type_translator,
            vcx.trait_registry,
            &vcx.procedure_registry,
            &vcx.const_registry,
        )
        .map(|x| (x, None)),
        ty::TyKind::Closure(_, _) => {
            let translator = signature::TX::new_closure(
                vcx.env,
                &meta,
                proc,
                &filtered_attrs,
                vcx.type_translator,
                vcx.trait_registry,
                &vcx.procedure_registry,
                &vcx.const_registry,
            );
            match translator {
                Ok((translator, info)) => {
                    // store the info to generate the trait impl later
                    let stored_info = procedures::ClosureInfo {
                        info,
                        generated_functions: Vec::new(),
                        generated_impls: Vec::new(),
                    };
                    Ok((translator, Some(stored_info)))
                },
                Err(err) => Err(err),
            }
        },
        _ => Err(base::TranslationError::UnknownError("unknown function kind".to_owned())),
    };

    if mode.is_only_spec() {
        // Only generate a spec
        match translator.and_then(|(tx, info)| tx.generate_spec().map(|x| (x, info))) {
            Ok((spec, info)) => {
                if vcx.env.tcx().dcx().has_errors().is_some() {
                    return false;
                }

                let spec_ref = vcx.fn_arena.alloc(spec);
                vcx.procedure_registry.provide_specced_function(f.to_def_id(), spec_ref);

                if let Some(info) = info {
                    let ordered_did = OrderedDefId::new(vcx.env.tcx(), f.to_def_id());
                    vcx.procedure_registry.closure_info.insert(ordered_did, info);
                }
                true
            },
            Err(base::TranslationError::FatalError(err)) => {
                println!("Encountered fatal cross-function error in translation: {:?}", err);
                println!("Aborting...");
                false
            },
            Err(err) => {
                println!("Encountered error: {:?}", err);
                println!("Skipping function {}", fname);
                if !rrconfig::skip_unsupported_features() {
                    exit_with_error(&format!(
                        "Encountered error when translating function {}, stopping...",
                        fname
                    ));
                }
                true
            },
        }
    } else {
        // Fully translate the function
        match translator.and_then(|(tx, info)| tx.translate(vcx.fn_arena).map(|x| (x, info))) {
            Ok((fun, info)) => {
                if vcx.env.tcx().dcx().has_errors().is_some() {
                    return false;
                }

                println!("Successfully translated {}", fname);
                vcx.procedure_registry.provide_translated_function(f.to_def_id(), fun);

                if let Some(info) = info {
                    let ordered_did = OrderedDefId::new(vcx.env.tcx(), f.to_def_id());
                    vcx.procedure_registry.closure_info.insert(ordered_did, info);
                }
                true
            },
            Err(base::TranslationError::FatalError(err)) => {
                println!("Encountered fatal cross-function error in translation: {:?}", err);
                println!("Aborting...");
                false
            },
            Err(err) => {
                println!("Encountered error: {:?}", err);
                println!("Skipping function {}", fname);
                if !rrconfig::skip_unsupported_features() {
                    exit_with_error(&format!(
                        "Encountered error when translating function {}, stopping...",
                        fname
                    ));
                }
                true
            },
        }
    }
}

fn exit_with_error(s: &str) {
    eprintln!("{s}");
    process::exit(-1);
}

/// Get all functions and closures in the current crate that have attributes on them and are not
/// skipped due to `rr::skip` attributes.
fn check_consider_function<'tcx>(
    vcx: &VerificationCtxt<'tcx, '_>,
    id: LocalDefId,
) -> Result<bool, base::TranslationError<'tcx>> {
    let env = vcx.env;
    if env.has_tool_attribute(id.to_def_id(), "skip") {
        warn!("Function {:?} will be skipped due to a rr::skip annotation", id);
        return Ok(false);
    }
    let has_any_attribute = env.has_any_tool_attribute(id.to_def_id());

    // check if this is an impl with a skip annotation
    let Some(impl_did) = env.tcx().impl_of_assoc(id.to_def_id()) else {
        return Ok(has_any_attribute);
    };

    if env.has_tool_attribute(impl_did, "skip") {
        warn!("Function {:?} will be skipped due to a rr::skip annotation on impl", id);
        return Ok(false);
    }

    // if there's no skip on the impl, having any attribute is sufficient
    if has_any_attribute {
        return Ok(true);
    }

    // check if this is an impl of a trait
    if !env.tcx().impl_is_of_trait(impl_did) {
        return Ok(false);
    }
    let trait_ref = env.tcx().impl_trait_ref(impl_did).skip_binder();
    let trait_did = trait_ref.def_id;

    // check if the impl has any attributes declared on it
    if env.has_any_tool_attribute(impl_did) {
        return Ok(true);
    }

    // Check if this is part of an impl of a derive trait for an ADT
    if !vcx.env.tcx().impl_is_of_trait(impl_did) {
        return Err(traits::Error::NotATraitImpl(impl_did).into());
    }
    let trait_ref = vcx.env.tcx().impl_trait_ref(impl_did).skip_binder();

    let self_ty = trait_ref.self_ty();
    let ty::TyKind::Adt(def, _) = self_ty.kind() else {
        return Ok(false);
    };

    // ADT has a skip annotation?
    if env.has_tool_attribute(def.did(), "skip") {
        return Ok(false);
    }
    // if there are no annotations, also skip
    if !env.has_any_tool_attribute(def.did()) {
        return Ok(false);
    }

    // otherwise, check if this is a Derive trait for which we have special support
    if traits::is_derive_trait_with_no_annotations(env.tcx(), trait_did) == Some(true) {
        return Ok(true);
    }

    // otherwise, check if this is for an ADT with derive annotations.
    if traits::is_derive_trait_with_annotations(env.tcx(), trait_did) == Some(true)
        && vcx.trait_registry.check_for_derive_trait_attrs(impl_did)?.is_some()
    {
        return Ok(true);
    }

    Ok(false)
}

/// Get constants in the current scope.
pub fn register_consts<'tcx>(vcx: &mut VerificationCtxt<'tcx, '_>) -> Result<(), String> {
    let statics = vcx.env.get_statics();

    for s in &statics {
        let ty: ty::EarlyBinder<'_, ty::Ty<'tcx>> = vcx.env.tcx().type_of(s.to_def_id());

        let const_attrs = attrs::filter_for_tool(vcx.env.get_attributes(s.to_def_id()));
        if const_attrs.is_empty() {
            continue;
        }

        let ty = ty.skip_binder();
        let scope = scope::Params::default();
        let typing_env = ty::TypingEnv::post_analysis(vcx.env.tcx(), s.to_def_id());
        match vcx
            .type_translator
            .translate_type_in_scope(&scope, typing_env, ty)
            .map_err(|x| format!("{:?}", x))
        {
            Ok(translated_ty) => {
                let _full_name = base::strip_coq_ident(&vcx.env.get_item_name(s.to_def_id()));

                let mut const_parser = VerboseConstAttrParser::new();
                let const_spec = const_parser.parse_const_attrs(*s, &const_attrs)?;

                let name = const_spec.name;
                let loc_name = format!("{name}_loc");

                let meta = code::StaticMeta {
                    ident: name,
                    loc_name,
                    ty: translated_ty,
                };
                let ordered_did = OrderedDefId::new(vcx.env.tcx(), s.to_def_id());
                vcx.const_registry.register_static(ordered_did, meta);
            },
            Err(e) => {
                println!("Warning: static {:?} has unsupported type, skipping: {:?}", s, e);
            },
        }
    }
    Ok(())
}

/// Register traits.
fn register_traits(vcx: &mut VerificationCtxt<'_, '_>) -> Result<(), String> {
    let traits = vcx.env.get_traits();

    // order according to dependencies first
    let deps = vcx.trait_registry.get_trait_deps(traits.as_slice());
    let ordered_traits = base::order_defs_with_deps(vcx.env.tcx(), &deps);

    let mut registered_traits = Vec::new();
    // first pre-register them to enable mutually recursive traits
    for t in &ordered_traits {
        let t = t.as_local().unwrap();

        info!("found trait {:?}", t);
        let mut all_have_annots = true;
        let mut some_has_annot = false;
        // check that all children have a specification
        let children = vcx.env.tcx().module_children_local(t);
        for c in children {
            if let hir::def::Res::Def(def_kind, def_id) = c.res
                && def_kind == hir::def::DefKind::AssocFn
            {
                if vcx.env.has_any_tool_attribute(def_id) {
                    some_has_annot = true;
                } else {
                    all_have_annots = false;
                }
            }
        }
        if !all_have_annots {
            if some_has_annot {
                println!("Warning: not all of trait {t:?}'s items are annotated, skipping");
            }
            continue;
        }

        registered_traits.push(t);

        vcx.trait_registry
            .preregister_trait(t)
            .map_err(|x| format!("{x:?}"))
            .map_err(|e| format!("{e:?}"))?;
    }
    // then properly translate them
    for t in registered_traits {
        vcx.trait_registry
            .register_trait(t, &mut vcx.procedure_registry)
            .map_err(|x| format!("{x:?}"))
            .map_err(|e| format!("{e:?}"))?;
    }
    Ok(())
}

/// Register trait impls of all registered traits.
/// Precondition: traits have already been registered.
fn register_trait_impls(vcx: &VerificationCtxt<'_, '_>) -> Result<(), String> {
    let trait_impl_ids = vcx.env.get_trait_impls();
    info!("Found trait impls: {:?}", trait_impl_ids);

    for trait_impl_id in trait_impl_ids {
        let did = trait_impl_id.to_def_id();
        let trait_ref = vcx.env.tcx().impl_trait_ref(did).skip_binder();
        let trait_did = trait_ref.def_id;

        // check if this trait has been registered
        if let Some(registered) = vcx.trait_registry.lookup_trait(trait_did) {
            // make sure all functions have a spec; otherwise, this is not a complete trait impl
            let assoc_items: &ty::AssocItems = vcx.env.tcx().associated_items(did);
            let mut all_specced = true;
            let assoc_items = traits::sort_assoc_items(vcx.env, assoc_items);
            for x in assoc_items {
                if x.tag() == ty::AssocTag::Fn {
                    // check if all functions have a specification
                    if let Some(mode) = vcx.procedure_registry.lookup_function_mode(x.def_id) {
                        all_specced = all_specced && mode.needs_spec();
                    } else {
                        all_specced = false;
                    }
                }
            }
            if !all_specced {
                continue;
            }

            // make names for the spec and inclusion proof
            let impl_lit = specs::traits::LiteralImpl::new(
                base::strip_coq_ident(&vcx.env.get_item_name(did)),
                registered.has_semantic_interp,
            );

            vcx.trait_registry
                .register_impl_shim(did, impl_lit)
                .map_err(|x| ToString::to_string(&x))?;
        }
    }

    Ok(())
}

/// Check if the `RefinedRust` closure library is available
fn are_closures_available(vcx: &VerificationCtxt<'_, '_>) -> bool {
    // let's check first if the closure library has been imported
    let check_clos = || -> Option<()> {
        let fnmut_did = search::get_closure_trait_did(vcx.env.tcx(), ty::ClosureKind::FnMut)?;
        let fn_did = search::get_closure_trait_did(vcx.env.tcx(), ty::ClosureKind::Fn)?;
        let fnonce_did = search::get_closure_trait_did(vcx.env.tcx(), ty::ClosureKind::FnOnce)?;

        vcx.trait_registry.lookup_trait(fnmut_did)?;
        vcx.trait_registry.lookup_trait(fn_did)?;
        vcx.trait_registry.lookup_trait(fnonce_did)?;

        Some(())
    };
    check_clos().is_some()
}

/// Register all closure impls.
fn register_closure_impls(vcx: &VerificationCtxt<'_, '_>) -> Result<(), String> {
    if !are_closures_available(vcx) {
        warn!("The RefinedRust closure library has not been imported, you will not be able to use closures.");
        return Ok(());
    }

    for closure_did in vcx.closures {
        let did = closure_did.to_def_id();

        // check if this closure is registered and will be verified
        let Some(meta) = vcx.procedure_registry.lookup_function(did) else {
            continue;
        };
        let mode = meta.get_mode();

        if !mode.needs_spec() {
            continue;
        }

        // check what kind of closure this is
        let clos_args = vcx.env.get_closure_args(closure_did.to_def_id());
        let kind = clos_args.kind();

        let make_impl = |kind| -> Result<(), String> {
            // make names for the spec and inclusion proof
            let impl_lit = specs::traits::LiteralImpl::new(
                base::strip_coq_ident(&format!("{}_{kind:?}", vcx.env.get_item_name(did))),
                false,
            );

            // create function meta
            let method_name = match kind {
                ty::ClosureKind::FnMut => "call_mut".to_owned(),
                ty::ClosureKind::Fn => "call".to_owned(),
                ty::ClosureKind::FnOnce => "call_once".to_owned(),
            };
            let fn_name = format!("{}_{method_name}", meta.get_name());
            let spec_name = format!("{fn_name}_spec");
            let code_name = format!("{fn_name}_code");
            let trait_req_incl_name = format!("{fn_name}_trait_req_incl");
            let fn_lit = procedures::Meta::new(
                spec_name,
                code_name,
                trait_req_incl_name,
                fn_name,
                procedures::Mode::Prove,
                true,
                false,
            );

            vcx.trait_registry
                .register_closure_impl(did, kind, impl_lit, fn_lit)
                .map_err(|x| ToString::to_string(&x))?;
            Ok(())
        };

        match kind {
            ty::ClosureKind::FnOnce => {
                make_impl(ty::ClosureKind::FnOnce)?;
            },
            ty::ClosureKind::FnMut => {
                make_impl(ty::ClosureKind::FnOnce)?;
                make_impl(ty::ClosureKind::FnMut)?;
            },
            ty::ClosureKind::Fn => {
                make_impl(ty::ClosureKind::FnOnce)?;
                make_impl(ty::ClosureKind::FnMut)?;
                make_impl(ty::ClosureKind::Fn)?;
            },
        }
    }

    Ok(())
}

/// Generate closure trait instances.
fn assemble_closure_impls<'tcx, 'rcx>(vcx: &mut VerificationCtxt<'tcx, 'rcx>) {
    if !are_closures_available(vcx) {
        return;
    }

    let generator =
        ClosureImplGenerator::new(vcx.env, vcx.trait_registry, vcx.type_translator, vcx.fn_arena).unwrap();

    for closure_did in vcx.closures {
        let closure_args = vcx.env.get_closure_args(closure_did.to_def_id());
        let kind = closure_args.kind();

        let Some(_) = vcx.trait_registry.lookup_closure_impl(closure_did.to_def_id(), kind) else {
            continue;
        };
        // in case the translation of the closure itself already failed, skip
        let Some(_) = vcx.procedure_registry.lookup_function_spec(closure_did.to_def_id()) else {
            continue;
        };

        let body_spec = vcx.procedure_registry.lookup_function_spec(closure_did.to_def_id()).unwrap();
        let meta = vcx.procedure_registry.lookup_function(closure_did.to_def_id()).unwrap();

        let process_impl = |to_impl: ty::ClosureKind, info: &procedures::ClosureImplInfo<'tcx, 'rcx>| {
            trace!("Generating closure impl {to_impl:?} for did = {closure_did:?}");
            // get the stored info
            let impl_info = vcx.trait_registry.get_closure_trait_impl_info(
                closure_did.to_def_id(),
                to_impl,
                info,
                closure_args,
            )?;

            trace!("Got closure info: {impl_info:?}");
            let (_, fn_meta) =
                vcx.trait_registry.lookup_closure_impl(closure_did.to_def_id(), to_impl).unwrap();

            let call_fn_def = generator.generate_call_function_for(
                closure_did.to_def_id(),
                &meta,
                &fn_meta,
                kind,
                to_impl,
                body_spec,
                &impl_info,
                info,
            )?;
            let name = generator.get_call_spec_record_entry_name(to_impl);

            trace!("Generated call fn");

            let mut methods = BTreeMap::new();
            let spec = call_fn_def.spec;
            methods.insert(name, specs::traits::InstanceMethodSpec::Defined(spec));

            let instance_spec = specs::traits::InstanceSpec::new(methods);

            let extra_context_items = body_spec.early_coq_params.clone();
            // assemble the spec and register it
            let spec = specs::traits::ImplSpec::new(impl_info, instance_spec, extra_context_items);

            trace!("Successfully generated closure impl");
            Ok((spec, call_fn_def))
        };

        let mut register_impl = |to_impl| {
            let ordered_did = OrderedDefId::new(vcx.env.tcx(), closure_did.to_def_id());
            let info = vcx.procedure_registry.closure_info.get_mut(&ordered_did).unwrap();
            let spec = process_impl(to_impl, &info.info);
            match spec {
                Ok((spec, fn_def)) => {
                    // store the generated call function
                    info.generated_functions.push(fn_def);
                    // store the trait impl
                    info.generated_impls.push(spec);
                },
                Err(base::TranslationError::FatalError(err)) => {
                    exit_with_error(&format!(
                        "Encountered error when translating {err:?} closure impl {closure_did:?}, stopping..."
                    ));
                },
                Err(err) => {
                    println!(
                        "Encountered error: {err:?} when translating closure impl {closure_did:?}, skipping"
                    );
                },
            }
        };

        match kind {
            ty::ClosureKind::FnOnce => {
                register_impl(ty::ClosureKind::FnOnce);
            },
            ty::ClosureKind::FnMut => {
                register_impl(ty::ClosureKind::FnOnce);
                register_impl(ty::ClosureKind::FnMut);
            },
            ty::ClosureKind::Fn => {
                register_impl(ty::ClosureKind::FnOnce);
                register_impl(ty::ClosureKind::FnMut);
                register_impl(ty::ClosureKind::Fn);
            },
        }
    }
}

/// Generate trait instances.
fn assemble_trait_impls<'tcx>(vcx: &mut VerificationCtxt<'tcx, '_>) {
    let trait_impl_ids = vcx.env.get_trait_impls();

    for trait_impl_id in trait_impl_ids {
        let did = trait_impl_id.to_def_id();
        let trait_ref = vcx.env.tcx().impl_trait_ref(did).skip_binder();
        let trait_did = trait_ref.def_id;

        // check if we registered this impl previously
        let Some(_) = vcx.trait_registry.lookup_impl(did) else { continue };

        if !vcx.env.tcx().impl_is_of_trait(did) {
            continue;
        }

        let tcx = vcx.env.tcx();

        trace!("Assembling trait impl {trait_impl_id:?}");

        let process_impl = || -> Result<(specs::traits::ImplSpec<'_>, BTreeSet<OrderedDefId>), base::TranslationError<'tcx>> {
            let (impl_info, deps, context_items) = vcx.trait_registry.get_trait_impl_info(did)?;
            let assoc_items: &'tcx ty::AssocItems = tcx.associated_items(did);
            trace!("impl assoc items: {assoc_items:?}");

            let trait_assoc_items: &'tcx ty::AssocItems = tcx.associated_items(trait_did);

            let mut methods = BTreeMap::new();

            let sorted_trait_assoc_items = traits::sort_assoc_items(vcx.env, trait_assoc_items);
            for x in sorted_trait_assoc_items {
                if x.tag() == ty::AssocTag::Fn {
                    let fn_item = assoc_items.filter_by_name_unhygienic_and_kind(
                        x.ident(tcx).name,
                        ty::AssocTag::Fn,
                    ).find(|y| y.trait_item_def_id() == Some(x.def_id));
                    trace!("Translating item {x:?}, fn_item = {fn_item:?}");

                    if let Some(fn_item) = fn_item {
                        if let Some(spec) = vcx.procedure_registry.lookup_function_spec(fn_item.def_id) {
                            methods.insert(x.name().as_str().to_owned(), specs::traits::InstanceMethodSpec::Defined(spec));
                        } else {
                            warn!("Incomplete specification for {}", fn_item.name());
                            return Err(base::TranslationError::IncompleteTraitImplSpec(did));
                        }
                    } else {
                        // this uses a default impl
                        let fn_name = base::strip_coq_ident(tcx.item_name(x.def_id).as_str());
                        let spec = specs::traits::InstantiatedFunctionSpec::new(impl_info.clone(), fn_name);

                        let assoc_item = trait_assoc_items.find_by_ident_and_kind(tcx, x.ident(tcx), ty::AssocTag::Fn, trait_did).unwrap();

                        trace!("assemble_trait_impls: trait_assoc_item = {:?}", assoc_item.def_id);
                        trace!("assemble_trait_impls: default spec: {spec:?}");
                        if let Some(default_meta) = vcx.procedure_registry.lookup_function(assoc_item.def_id) {
                            // now build the generic scope for this item.
                            let ty = tcx.type_of(assoc_item.def_id).instantiate_identity();
                            let ty::TyKind::FnDef(_, params) = ty.kind() else {
                                unimplemented!();
                            };
                            let mut generics = scope::Params::new_from_generics(tcx, params, Some(assoc_item.def_id));
                            generics.add_param_env(assoc_item.def_id, vcx.env, vcx.type_translator, vcx.trait_registry)?;
                            // TODO: We don't respect dependencies of the direct scope on the
                            // surrounding scope here. For instance for assoc type constraints.
                            //
                            // Dirty fix: I introduce let bindings in the translation for the inst
                            // => let's just do this for now.
                            //
                            // Better: we should already substitute suitably in Rust.
                            // But how do I do that? This seems a bit difficult.

                            // add late bounds
                            let sig = ty.fn_sig(vcx.env.tcx());
                            let bound_vars = sig.bound_vars();
                            let mut bound_regions = Vec::new();
                            for x in bound_vars {
                                bound_regions.push(x.expect_region());
                            }
                            drop(generics.translate_bound_regions(tcx, &bound_regions));

                            let scope: specs::GenericScope<'_> = generics.into();

                            methods.insert(x.name().as_str().to_owned(), specs::traits::InstanceMethodSpec::DefaultSpec(Box::new(spec), scope, default_meta.get_spec_name().to_owned()));
                        }
                        else {
                            // this can happen for incompletely specified traits from stdlib, let's
                            // ignore this
                        }
                    }
                }
            }
            let instance_spec = specs::traits::InstanceSpec::new(methods);

            // assemble the spec and register it
            let spec = specs::traits::ImplSpec::new(impl_info,
                instance_spec,
                context_items);
            Ok((spec, deps))
        };

        let spec = process_impl();
        match spec {
            Ok((spec, deps)) => {
                let ordered_did = OrderedDefId::new(vcx.env.tcx(), did);
                vcx.trait_impls.insert(ordered_did, spec);
                vcx.trait_impl_deps.insert(ordered_did, deps);
            },
            Err(base::TranslationError::FatalError(err)) => {
                exit_with_error(&format!(
                    "Encountered error when translating {err:?} trait impl {did:?}, stopping..."
                ));
            },
            Err(err) => {
                println!("Encountered error: {err:?} when translating trait impl {did:?}, skipping");
            },
        }
    }
}

/// Get and parse all module attributes.
fn get_module_attributes(env: &Environment<'_>) -> Result<BTreeMap<OrderedDefId, ModuleAttrs>, String> {
    let modules = env.get_modules();
    let mut attrs = BTreeMap::new();
    info!("collected modules: {:?}", modules);

    for m in &modules {
        let module_attrs = attrs::filter_for_tool(env.get_attributes(m.to_def_id()));
        let mut module_parser = VerboseModuleAttrParser::new();
        let module_spec = module_parser.parse_module_attrs(*m, &module_attrs)?;
        let ordered_did = OrderedDefId::new(env.tcx(), m.to_def_id());
        attrs.insert(ordered_did, module_spec);
    }

    Ok(attrs)
}

fn add_builtin_shims(registry: &mut shim_registry::SR<'_>) {
    let phantom_data_shim = shim_registry::AdtShim {
        path: registry.intern_path(vec!["core".to_owned(), "marker".to_owned(), "PhantomData".to_owned()]),
        refinement_type: "core_marker_PhantomData_rt".to_owned(),
        syn_type: "core_marker_PhantomData_sls".to_owned(),
        sem_type: "core_marker_PhantomData_ty".to_owned(),
        info: specs::types::AdtShimInfo::empty(),
    };

    registry.add_adt_shim(phantom_data_shim);
}

/// Translate a crate, creating a `VerificationCtxt` in the process.
pub fn generate_coq_code<'tcx, F>(tcx: ty::TyCtxt<'tcx>, continuation: F) -> Result<(), String>
where
    F: Fn(VerificationCtxt<'tcx, '_>),
{
    let env = Environment::new(tcx);
    let env: &Environment<'_> = &*Box::leak(Box::new(env));

    // get crate attributes
    let crate_attrs = tcx.hir_krate_attrs();
    let crate_attrs = attrs::filter_for_tool(crate_attrs);
    info!("Found crate attributes: {:?}", crate_attrs);
    // parse crate attributes
    let mut crate_parser = VerboseCrateAttrParser::new();
    let crate_spec = crate_parser.parse_crate_attrs(&crate_attrs)?;

    let path_prefix = crate_spec.prefix.unwrap_or_else(|| "refinedrust.examples".to_owned());
    info!("Setting Coq path prefix: {:?}", path_prefix);

    let package = crate_spec.package;
    info!("Setting dune package: {:?}", package);

    // get module attributes
    let module_attrs = get_module_attributes(env)?;

    // process exports
    let mut exports: BTreeSet<coq::module::Export> = BTreeSet::new();

    exports.extend(crate_spec.exports);

    for module_attr in module_attrs.values() {
        exports.extend(module_attr.exports.clone());
    }

    info!("Exporting extra Coq files: {:?}", exports);

    // process includes
    let mut includes: BTreeSet<String> = BTreeSet::new();
    crate_spec.includes.into_iter().map(|name| includes.insert(name)).count();
    module_attrs
        .values()
        .map(|attrs| attrs.includes.iter().map(|name| includes.insert(name.to_owned())).count())
        .count();
    info!("Including RefinedRust modules: {:?}", includes);
    // process export_includes
    let mut export_includes: BTreeSet<String> = BTreeSet::new();
    crate_spec.export_includes.into_iter().map(|name| export_includes.insert(name)).count();
    module_attrs
        .into_values()
        .map(|attrs| attrs.export_includes.into_iter().map(|name| export_includes.insert(name)).count())
        .count();
    info!("Exporting RefinedRust modules: {:?}", export_includes);

    let functions = env.get_procedures();
    let closures = env.get_closures();
    info!("Found {} function(s) and {} closure(s)", functions.len(), closures.len());

    let struct_arena = Arena::new();
    let enum_arena = Arena::new();
    let shim_arena = Arena::new();
    let trait_arena = Arena::new();
    let trait_impl_arena = Arena::new();
    let trait_use_arena = Arena::new();
    let fn_spec_arena = Arena::new();
    let type_translator = types::TX::new(env, &struct_arena, &enum_arena, &shim_arena);
    let trait_registry =
        registry::TR::new(env, &trait_arena, &trait_impl_arena, &trait_use_arena, &fn_spec_arena);
    // establish the cycle
    type_translator.provide_trait_registry(&trait_registry);
    trait_registry.provide_type_translator(&type_translator);

    let procedure_registry = procedures::Scope::new(tcx);
    let shim_string_arena = Arena::new();
    let mut shim_registry = shim_registry::SR::empty(&shim_string_arena);

    // add builtin shims
    add_builtin_shims(&mut shim_registry);

    // add includes to the shim registry
    let library_load_paths = rrconfig::lib_load_paths();
    info!("Loading libraries from {:?}", library_load_paths);
    let found_libs = shims::scan_loadpaths(&library_load_paths).map_err(|e| e.to_string())?;
    info!("Found the following RefinedRust libraries in the loadpath: {:?}", found_libs);

    let mut included_libs = BTreeSet::new();
    while !includes.is_empty() {
        let incl = includes.iter().next().unwrap().to_owned();
        includes.remove(&incl);
        let Some(p) = found_libs.get(&incl) else {
            println!("Warning: did not find library {} in loadpath", incl);
            continue;
        };
        included_libs.insert(incl);

        let f = File::open(p).map_err(|e| e.to_string())?;
        if let Some(new_includes) = shim_registry.add_source(f).map_err(|e| e.to_string())? {
            for incl in new_includes {
                if !included_libs.contains(&incl) {
                    includes.insert(incl);
                }
            }
        }
    }

    let mut export_included_libs = BTreeSet::new();
    while !export_includes.is_empty() {
        let incl = export_includes.iter().next().unwrap().to_owned();
        export_includes.remove(&incl);
        let Some(p) = found_libs.get(&incl) else {
            println!("Warning: did not find library {} in loadpath", incl);
            continue;
        };
        let skip = included_libs.contains(&incl);
        export_included_libs.insert(incl);

        if skip {
            continue;
        }

        let f = File::open(p).map_err(|e| e.to_string())?;
        if let Some(new_includes) = shim_registry.add_source(f).map_err(|e| e.to_string())? {
            for incl in new_includes {
                if !included_libs.contains(&incl) && !export_included_libs.contains(&incl) {
                    export_includes.insert(incl);
                }
            }
        }
    }

    // first register names for all the procedures, to resolve mutual dependencies
    let mut vcx = VerificationCtxt {
        env,
        functions: functions.as_slice(),
        closures: closures.as_slice(),
        type_translator: &type_translator,
        trait_registry: &trait_registry,
        procedure_registry,
        lib_exports: export_included_libs,
        extra_exports: exports.into_iter().map(|x| (x, false)).collect(),
        extra_dependencies: BTreeSet::new(),
        coq_path_prefix: path_prefix,
        shim_registry,
        dune_package: package,
        const_registry: consts::Scope::empty(),
        trait_impls: BTreeMap::new(),
        trait_impl_deps: BTreeMap::new(),
        fn_arena: &fn_spec_arena,
    };

    // this needs to be first, in order to ensure consistent ADT use
    register_shims(&mut vcx).map_err(|x| x.to_string())?;

    register_functions(&mut vcx).map_err(|x| x.to_string())?;

    register_traits(&mut vcx)?;

    register_trait_impls(&vcx)?;

    register_closure_impls(&vcx)?;

    // after trait impls, as type translation may depend on trait impls
    register_consts(&mut vcx)?;

    translate_functions(&mut vcx);

    // important: happens after all functions have been translated, as this uses the translated
    // function specs
    assemble_trait_impls(&mut vcx);

    assemble_closure_impls(&mut vcx);

    continuation(vcx);

    Ok(())
}

/// # Safety
///
/// See the module level comment in `crate::environment::mir_storage`.
pub unsafe fn store_mir_body<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: LocalDefId,
    body_with_facts: BodyWithBorrowckFacts<'tcx>,
) {
    // SAFETY: See the module level comment.
    unsafe {
        environment::mir_storage::store_mir_body(tcx, def_id, body_with_facts);
    }
}
