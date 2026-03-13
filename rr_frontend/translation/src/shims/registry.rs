// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Registry of shims for Rust functions that get mapped to custom `RefinedRust`
//! implementations.
//! Provides deserialization from a JSON file defining this registry.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io::{self, BufReader, BufWriter};

use derive_more::{Display, From};
use log::info;
use radium::{coq, specs};
use serde::{Deserialize, Serialize};
use typed_arena::Arena;

use crate::shims::flat;

type Path<'a> = Vec<&'a str>;

mod remote {
    use super::*;

    #[derive(Serialize, Deserialize)]
    #[serde(remote = "specs::traits::LiteralImpl")]
    pub(super) struct LiteralImpl {
        #[serde(getter = "Self::name")]
        name: String,

        #[serde(getter = "Self::has_semantic_interp")]
        has_semantic_interp: bool,
    }

    impl LiteralImpl {
        fn name(literal_impl: &specs::traits::LiteralImpl) -> String {
            literal_impl
                .spec_record()
                .strip_suffix("_spec")
                .unwrap_or_else(|| unreachable!("This is the reverse function of `spec_record`"))
                .to_owned()
        }

        fn has_semantic_interp(literal_impl: &specs::traits::LiteralImpl) -> bool {
            Option::is_some(&literal_impl.spec_semantic())
        }
    }

    impl From<LiteralImpl> for specs::traits::LiteralImpl {
        fn from(literal_impl: LiteralImpl) -> Self {
            Self::new(literal_impl.name, literal_impl.has_semantic_interp)
        }
    }

    #[derive(Serialize, Deserialize)]
    #[serde(remote = "specs::types::AdtShimInfo")]
    pub(super) struct AdtShimInfo {
        #[serde(getter = "Self::enum_name")]
        enum_name: Option<String>,

        #[serde(getter = "Self::needs_trait_attrs")]
        needs_trait_attrs: bool,

        #[serde(getter = "Self::atomic_inner_st")]
        atomic_inner_st: Option<String>,
    }

    impl AdtShimInfo {
        fn enum_name(adt_shim_info: &specs::types::AdtShimInfo) -> Option<String> {
            adt_shim_info.enum_name().cloned()
        }

        const fn needs_trait_attrs(adt_shim_info: &specs::types::AdtShimInfo) -> bool {
            adt_shim_info.needs_trait_attrs()
        }

        fn atomic_inner_st(adt_shim_info: &specs::types::AdtShimInfo) -> Option<String> {
            adt_shim_info.atomic_inner_st().map(str::to_owned)
        }
    }

    impl From<AdtShimInfo> for specs::types::AdtShimInfo {
        fn from(adt_shim_info: AdtShimInfo) -> Self {
            Self::new(adt_shim_info.enum_name, adt_shim_info.needs_trait_attrs, adt_shim_info.atomic_inner_st)
        }
    }
}

/// A file entry for a function/method shim.
#[derive(Serialize, Deserialize)]
struct ShimFunctionEntry {
    /// The rustc path for this symbol.
    path: Vec<String>,
    /// a kind: either "method" or "function"
    kind: String,
    /// the basis name to use for generated Coq names
    name: String,
    /// the Coq name of the spec
    spec: String,
    /// the Coq name of the trait assumption inclusion for this function
    trait_req_incl: String,
}

/// A file entry for a trait shim.
#[derive(Serialize, Deserialize)]
struct ShimTraitEntry {
    /// The rustc path for this symbol
    path: Vec<String>,
    /// a kind: always "trait"
    kind: String,
    /// name of the trait
    name: String,
    /// whether this trait has a semantic interpretation
    has_semantic_interp: bool,
    /// whether the attrs record is dependent
    attrs_dependent: bool,
    /// allowed attributes on impls of this trait
    allowed_attrs: Vec<String>,
    /// definition names for the canonical trait linking assumption for each method
    method_trait_incl_decls: BTreeMap<String, String>,
}

/// A file entry for a trait method implementation.
#[derive(Serialize, Deserialize)]
struct ShimTraitImplEntry {
    /// The rustc path for the trait
    trait_path: flat::PathWithArgs,
    /// for which type is this implementation?
    for_type: flat::Type,
    // TODO: additional constraints like the required clauses for disambiguation
    /// a kind: always `trait_impl`
    kind: String,

    /// map from method names to (base name, specification name, trait incl name)
    method_specs: BTreeMap<String, (String, String, String)>,

    #[serde(flatten)]
    #[serde(with = "remote::LiteralImpl")]
    specs: specs::traits::LiteralImpl,
}

/// A file entry for an adt shim.
#[derive(Serialize, Deserialize)]
struct ShimAdtEntry {
    /// The rustc path for this symbol.
    path: Vec<String>,
    /// always "adt"
    kind: String,
    /// the Coq name of the syntactic type
    syntype: String,
    /// the Coq name of the refinement type
    rtype: String,
    /// the Coq name of the semantic type
    semtype: String,

    /// more meta information
    #[serde(with = "remote::AdtShimInfo")]
    info: specs::types::AdtShimInfo,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) enum ShimKind {
    Method,
    Function,
    TraitImpl,
    Adt,
    Trait,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) struct FunctionShim<'a> {
    pub path: Path<'a>,
    pub is_method: bool,
    pub name: String,
    pub spec_name: String,
    pub trait_req_incl_name: String,
}

impl<'a> From<FunctionShim<'a>> for ShimFunctionEntry {
    fn from(shim: FunctionShim<'a>) -> Self {
        Self {
            path: shim.path.iter().map(|x| (*x).to_owned()).collect(),
            kind: if shim.is_method { "method".to_owned() } else { "function".to_owned() },
            name: shim.name,
            spec: shim.spec_name,
            trait_req_incl: shim.trait_req_incl_name,
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) struct TraitImplShim {
    pub trait_path: flat::PathWithArgs,
    pub for_type: flat::Type,
    pub method_specs: BTreeMap<String, (String, String, String)>,
    pub specs: specs::traits::LiteralImpl,
}

impl From<TraitImplShim> for ShimTraitImplEntry {
    fn from(shim: TraitImplShim) -> Self {
        Self {
            trait_path: shim.trait_path,
            for_type: shim.for_type,
            method_specs: shim.method_specs,
            kind: "trait_impl".to_owned(),
            specs: shim.specs,
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) struct TraitShim<'a> {
    pub path: Path<'a>,
    pub name: String,
    pub has_semantic_interp: bool,
    pub attrs_dependent: bool,
    pub allowed_attrs: Vec<String>,
    pub method_trait_incl_decls: BTreeMap<String, String>,
}

impl<'a> From<TraitShim<'a>> for ShimTraitEntry {
    fn from(shim: TraitShim<'a>) -> Self {
        Self {
            path: shim.path.iter().map(|x| (*x).to_owned()).collect(),
            kind: "trait".to_owned(),
            name: shim.name,
            has_semantic_interp: shim.has_semantic_interp,
            attrs_dependent: shim.attrs_dependent,
            allowed_attrs: shim.allowed_attrs,
            method_trait_incl_decls: shim.method_trait_incl_decls,
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) struct AdtShim<'a> {
    pub path: Path<'a>,
    pub refinement_type: String,
    pub syn_type: String,
    pub sem_type: String,
    pub info: specs::types::AdtShimInfo,
}

impl<'a> From<AdtShim<'a>> for ShimAdtEntry {
    fn from(shim: AdtShim<'a>) -> Self {
        Self {
            path: shim.path.iter().map(|x| (*x).to_owned()).collect(),
            kind: "adt".to_owned(),
            syntype: shim.syn_type,
            semtype: shim.sem_type,
            rtype: shim.refinement_type,
            info: shim.info,
        }
    }
}

#[derive(Debug, From, Display)]
pub(crate) enum Error {
    #[from]
    #[display("Deserialization error: {:?}", _0)]
    Deserialize(serde_json::Error),
    #[display("Missing field: {}", _0)]
    MissingField(String),
    #[from]
    #[display("IO error: {:?}", _0)]
    Io(io::Error),
    #[display("Expected type {} for attribute {}", attribute, expected)]
    Type { attribute: String, expected: String },
    #[display("Missing attribute: {}", _0)]
    MissingAttribute(String),
    #[display("Not an object")]
    NotAnObject,
    #[display("Unknown shim kind: {}", _0)]
    UnknownShimKind(String),
}

/// Registry of function shims loaded by the user. Substitutes path to the function/method with a
/// code definition name and a spec name.
pub(crate) struct SR<'a> {
    arena: &'a Arena<String>,

    /// function/method shims
    function_shims: Vec<FunctionShim<'a>>,

    /// adt shims
    adt_shims: Vec<AdtShim<'a>>,

    /// extra exports
    exports: Vec<coq::module::Export>,

    /// trait shims
    trait_shims: Vec<TraitShim<'a>>,

    /// trait impl shims
    trait_impl_shims: Vec<TraitImplShim>,

    /// extra module dependencies
    dependencies: BTreeSet<coq::module::DirPath>,
}

impl<'a> SR<'a> {
    fn get_shim_kind(v: &serde_json::Value) -> Result<ShimKind, Error> {
        let obj = v.as_object().ok_or(Error::NotAnObject)?;
        let vk = obj.get("kind").ok_or_else(|| Error::MissingField("kind".to_owned()))?;
        let kind_str = vk.as_str().ok_or_else(|| Error::Type {
            attribute: "kind".to_owned(),
            expected: "str".to_owned(),
        })?;

        match kind_str {
            "function" => Ok(ShimKind::Function),
            "method" => Ok(ShimKind::Method),
            "adt" => Ok(ShimKind::Adt),
            "trait" => Ok(ShimKind::Trait),
            "trait_impl" => Ok(ShimKind::TraitImpl),
            k => Err(Error::UnknownShimKind(k.to_owned())),
        }
    }

    pub(crate) fn intern_path(&self, p: Vec<String>) -> Path<'a> {
        let mut path = Vec::new();
        for pc in p {
            let pc = self.arena.alloc(pc);
            path.push(pc.as_str());
        }
        path
    }

    pub(crate) const fn empty(arena: &'a Arena<String>) -> Self {
        Self {
            arena,
            function_shims: Vec::new(),
            adt_shims: Vec::new(),
            exports: Vec::new(),
            dependencies: BTreeSet::new(),
            trait_shims: Vec::new(),
            trait_impl_shims: Vec::new(),
        }
    }

    pub(crate) fn add_adt_shim(&mut self, shim: AdtShim<'a>) {
        self.adt_shims.push(shim);
    }

    pub(crate) fn add_source(&mut self, f: File) -> Result<Option<BTreeSet<String>>, Error> {
        info!("Adding file {f:?}");
        let reader = BufReader::new(f);
        let deser: serde_json::Value = serde_json::from_reader(reader)?;

        // We support both directly giving the items array, or also specifying a path to import
        let (v, export_libs) = match deser {
            serde_json::Value::Object(obj) => {
                let path = obj
                    .get("refinedrust_path")
                    .ok_or_else(|| Error::MissingAttribute("refinedrust_path".to_owned()))?
                    .as_str()
                    .ok_or_else(|| Error::Type {
                        attribute: "refinedrust_path".to_owned(),
                        expected: "str".to_owned(),
                    })?;

                let module = obj
                    .get("refinedrust_module")
                    .ok_or_else(|| Error::MissingAttribute("refinedrust_module".to_owned()))?
                    .as_str()
                    .ok_or_else(|| Error::Type {
                        attribute: "refinedrust_module".to_owned(),
                        expected: "str".to_owned(),
                    })?;

                obj.get("refinedrust_name")
                    .ok_or_else(|| Error::MissingAttribute("refinedrust_name".to_owned()))?
                    .as_str()
                    .ok_or_else(|| Error::Type {
                        attribute: "refinedrust_name".to_owned(),
                        expected: "str".to_owned(),
                    })?;

                self.exports.push(coq::module::Export::new(vec![module]).from(vec![path]));

                let coq_dependencies = obj
                    .get("module_dependencies")
                    .ok_or_else(|| Error::MissingAttribute("module_dependencies".to_owned()))?
                    .as_array()
                    .ok_or_else(|| Error::Type {
                        attribute: "module_dependencies".to_owned(),
                        expected: "array".to_owned(),
                    })?;

                for dependency in coq_dependencies {
                    let path = dependency.as_str().ok_or_else(|| Error::Type {
                        attribute: "element of module_dependencies".to_owned(),
                        expected: "str".to_owned(),
                    })?;

                    self.dependencies.insert(coq::module::DirPath::from(vec![path]));
                }

                let mut export_libs = BTreeSet::new();
                let export_lib_arr = obj
                    .get("export_libs")
                    .ok_or_else(|| Error::MissingAttribute("export_libs".to_owned()))?
                    .as_array()
                    .ok_or_else(|| Error::Type {
                        attribute: "export_libs".to_owned(),
                        expected: "array".to_owned(),
                    })?;
                for dependency in export_lib_arr {
                    let dep = dependency.as_str().ok_or_else(|| Error::Type {
                        attribute: "element of export_libs".to_owned(),
                        expected: "str".to_owned(),
                    })?;
                    export_libs.insert(dep.to_owned());
                }

                let items = obj
                    .get("items")
                    .ok_or_else(|| Error::MissingAttribute("items".to_owned()))?
                    .as_array()
                    .ok_or_else(|| Error::Type {
                        attribute: "items".to_owned(),
                        expected: "array".to_owned(),
                    })?
                    .clone();
                (items, Some(export_libs))
            },

            serde_json::Value::Array(arr) => (arr, None),

            _ => {
                return Err(Error::Type {
                    attribute: String::new(),
                    expected: "array or object".to_owned(),
                });
            },
        };

        for i in v {
            let kind = Self::get_shim_kind(&i)?;

            match kind {
                ShimKind::Adt => {
                    let b: ShimAdtEntry = serde_json::value::from_value(i)?;
                    let path = self.intern_path(b.path);
                    let entry = AdtShim {
                        path,
                        syn_type: b.syntype,
                        sem_type: b.semtype,
                        refinement_type: b.rtype,
                        info: b.info,
                    };

                    self.adt_shims.push(entry);
                },
                ShimKind::Function | ShimKind::Method => {
                    let b: ShimFunctionEntry = serde_json::value::from_value(i)?;
                    let path = self.intern_path(b.path);
                    let entry = FunctionShim {
                        path,
                        is_method: kind == ShimKind::Method,
                        name: b.name,
                        spec_name: b.spec,
                        trait_req_incl_name: b.trait_req_incl,
                    };

                    self.function_shims.push(entry);
                },
                ShimKind::TraitImpl => {
                    let b: ShimTraitImplEntry = serde_json::value::from_value(i)?;
                    let entry = TraitImplShim {
                        trait_path: b.trait_path,
                        for_type: b.for_type,
                        method_specs: b.method_specs,
                        specs: b.specs,
                    };

                    self.trait_impl_shims.push(entry);
                },
                ShimKind::Trait => {
                    let b: ShimTraitEntry = serde_json::value::from_value(i)?;
                    let entry = TraitShim {
                        path: self.intern_path(b.path),
                        name: b.name,
                        has_semantic_interp: b.has_semantic_interp,
                        attrs_dependent: b.attrs_dependent,
                        allowed_attrs: b.allowed_attrs,
                        method_trait_incl_decls: b.method_trait_incl_decls,
                    };

                    self.trait_shims.push(entry);
                },
            }
        }

        Ok(export_libs)
    }

    pub(crate) fn get_function_shims(&self) -> &[FunctionShim<'_>] {
        &self.function_shims
    }

    pub(crate) fn get_adt_shims(&self) -> &[AdtShim<'_>] {
        &self.adt_shims
    }

    pub(crate) fn get_extra_exports(&self) -> &[coq::module::Export] {
        &self.exports
    }

    pub(crate) fn get_trait_shims(&self) -> &[TraitShim<'_>] {
        &self.trait_shims
    }

    pub(crate) fn get_trait_impl_shims(&self) -> &[TraitImplShim] {
        &self.trait_impl_shims
    }

    pub(crate) const fn get_extra_dependencies(&self) -> &BTreeSet<coq::module::DirPath> {
        &self.dependencies
    }
}

/// Write serialized representation of shims to a file.
pub(crate) fn write_shims<'a>(
    f: File,
    load_path: &str,
    load_module: &str,
    name: &str,
    module_dependencies: &BTreeSet<coq::module::DirPath>,
    export_libs: &BTreeSet<String>,
    adt_shims: Vec<AdtShim<'a>>,
    function_shims: Vec<FunctionShim<'a>>,
    trait_shims: Vec<TraitShim<'_>>,
    trait_impl_shims: Vec<TraitImplShim>,
) {
    let writer = BufWriter::new(f);

    let mut values = Vec::new();
    for x in adt_shims {
        let x: ShimAdtEntry = x.into();
        values.push(serde_json::to_value(x).unwrap());
    }
    for x in function_shims {
        let x: ShimFunctionEntry = x.into();
        values.push(serde_json::to_value(x).unwrap());
    }
    for x in trait_shims {
        let x: ShimTraitEntry = x.into();
        values.push(serde_json::to_value(x).unwrap());
    }
    for x in trait_impl_shims {
        let x: ShimTraitImplEntry = x.into();
        values.push(serde_json::to_value(x).unwrap());
    }

    let array_val = serde_json::Value::Array(values);

    info!("write_shims: writing entries {:?}", array_val);

    let module_dependencies: Vec<_> = module_dependencies.iter().map(ToString::to_string).collect();

    let object = serde_json::json!({
        "refinedrust_path": load_path,
        "refinedrust_module": load_module,
        "refinedrust_name": name,
        "module_dependencies": module_dependencies,
        "export_libs": export_libs,
        "items": array_val
    });

    serde_json::to_writer_pretty(writer, &object).unwrap();
}

/// Check if this file declares a `RefinedRust` module.
pub(crate) fn is_valid_refinedrust_module(f: File) -> Option<String> {
    let reader = BufReader::new(f);
    let deser: serde_json::Value = serde_json::from_reader(reader).unwrap();

    // We support both directly giving the items array, or also specifying a path to import
    match deser {
        serde_json::Value::Object(obj) => {
            let path = obj.get("refinedrust_path")?;
            let _path = path.as_str()?;

            let module = obj.get("refinedrust_module")?;
            let _module = module.as_str()?;

            let name = obj.get("refinedrust_name")?;
            let name = name.as_str()?;

            Some(name.to_owned())
        },
        _ => None,
    }
}
