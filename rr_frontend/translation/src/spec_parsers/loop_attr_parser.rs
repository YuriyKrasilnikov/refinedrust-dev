// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{BTreeMap, HashSet};

use attribute_parse::{MToken, parse};
use parse::{Parse, Peek as _};
use radium::{code, coq, model, specs};
use rr_rustc_interface::hir;
use rr_rustc_interface::middle::mir;

use crate::spec_parsers::parse_utils::{
    IProp, ParamLookup, RRParams, RustPath, RustPathElem, attr_args_tokens, str_err,
};

/// Parse attributes on a const.
/// Permitted attributes:
/// TODO
pub(crate) trait LoopAttrParser {
    fn parse_loop_attrs<'a>(&'a mut self, attrs: &'a [&'a hir::AttrItem]) -> Result<specs::LoopSpec, String>;
}

/// Representation of the `IProps` that can appear in a requires or ensures clause.
enum MetaIProp {
    /// `#[rr::requires("..")]` or `#[rr::requires("Ha" : "..")]`
    Pure(String, Option<String>),
    /// `#[rr::requires(#iris "..")]`
    Iris(coq::iris::IProp),
    /// `#[rr::requires(#type "l" : "rfn" @ "ty")]`
    Type(specs::TyOwnSpec),
}

impl<'def, T: ParamLookup<'def>> Parse<T> for MetaIProp {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        if parse::Pound::peek(stream) {
            stream.parse::<_, MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = stream.parse(meta)?;
            match macro_cmd.value().as_str() {
                "type" => {
                    let loc_str: parse::LitStr = stream.parse(meta)?;
                    let (loc_str, mut annot_meta) = meta.process_coq_literal(&loc_str.value());

                    stream.parse::<_, MToken![:]>(meta)?;

                    let rfn_str: parse::LitStr = stream.parse(meta)?;
                    let (rfn_str, annot_meta2) = meta.process_coq_literal(&rfn_str.value());

                    annot_meta.join(&annot_meta2);

                    stream.parse::<_, MToken![@]>(meta)?;

                    let type_str: parse::LitStr = stream.parse(meta)?;
                    let (type_str, annot_meta3) = meta.process_coq_literal(&type_str.value());
                    annot_meta.join(&annot_meta3);

                    let spec = specs::TyOwnSpec::new(loc_str, rfn_str, type_str, false, annot_meta);
                    Ok(Self::Type(spec))
                },
                "iris" => {
                    let prop: IProp = stream.parse(meta)?;
                    Ok(Self::Iris(prop.into()))
                },
                _ => Err(parse::Error::OtherErr(
                    stream.pos().unwrap(),
                    format!("invalid macro command: {:?}", macro_cmd.value()),
                )),
            }
        } else {
            let name_or_prop_str: parse::LitStr = stream.parse(meta)?;
            if parse::Colon::peek(stream) {
                // this is a name
                let name_str = name_or_prop_str.value();

                stream.parse::<_, MToken![:]>(meta)?;

                let pure_prop: parse::LitStr = stream.parse(meta)?;
                let (pure_str, _annot_meta) = meta.process_coq_literal(&pure_prop.value());
                // TODO: should we use annot_meta?

                Ok(Self::Pure(pure_str, Some(name_str)))
            } else {
                // this is a
                let (lit, _) = meta.process_coq_literal(&name_or_prop_str.value());
                Ok(Self::Pure(lit, None))
            }
        }
    }
}

impl From<MetaIProp> for coq::iris::IProp {
    fn from(meta: MetaIProp) -> Self {
        match meta {
            MetaIProp::Pure(p, name) => match name {
                None => Self::Pure(Box::new(coq::term::Term::Literal(p))),
                Some(n) => Self::Pure(Box::new(coq::term::Term::UserDefined(model::Term::WithName(
                    Box::new(coq::term::Term::Literal(p)),
                    n,
                )))),
            },
            MetaIProp::Iris(p) => p,
            MetaIProp::Type(spec) => {
                let lit = spec.fmt_owned("π");
                Self::Atom(lit)
            },
        }
    }
}

/// Invariant variable refinement declaration
#[derive(Debug)]
struct InvVar {
    local: String,
    rfn: Option<String>,
}

impl<'def, T: ParamLookup<'def>> Parse<T> for InvVar {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let local_str: parse::LitStr = stream.parse(meta)?;
        let local_str = local_str.value();

        let rfn_str = if parse::Colon::peek(stream) {
            stream.parse::<_, MToken![:]>(meta)?;

            let rfn_str: parse::LitStr = stream.parse(meta)?;
            let (rfn_str, _) = meta.process_coq_literal(&rfn_str.value());
            Some(rfn_str)
        } else {
            None
        };

        Ok(Self {
            local: local_str,
            rfn: rfn_str,
        })
    }
}

/// Info about the iterator we are iterating over, in case of `for` loops.
pub(crate) struct LoopIteratorInfo<'def> {
    pub(crate) iterator_variable: mir::Local,
    pub(crate) binder_name: String,
    pub(crate) history_name: String,
    pub(crate) iter_spec: specs::traits::ReqInst<'def>,
}

struct LoopMetaInfo<'def, 'a, T> {
    scope: &'a T,
    iterator_info: Option<LoopIteratorInfo<'def>>,
}

impl<'def, T: ParamLookup<'def>> ParamLookup<'def> for LoopMetaInfo<'def, '_, T> {
    fn lookup_ty_param(&self, path: &RustPath) -> Option<specs::Type<'def>> {
        self.scope.lookup_ty_param(path)
    }

    fn lookup_lft(&self, lft: &str) -> Option<&specs::LftParam> {
        self.scope.lookup_lft(lft)
    }

    fn lookup_literal(&self, path: &RustPath) -> Option<String> {
        #[expect(clippy::collapsible_if)]
        if let Some(info) = &self.iterator_info {
            if path.len() == 1 {
                let RustPathElem::AssocItem(it) = &path[0];
                match it.as_str() {
                    "Iter" => {
                        return Some(info.binder_name.clone());
                    },
                    "Hist" => {
                        return Some(info.history_name.clone());
                    },
                    "IterAttrs" => {
                        let attr_term = info.iter_spec.get_attr_term();
                        let term = format!("({attr_term})");
                        return Some(term);
                    },
                    "IterNext" => {
                        let attr_term = info.iter_spec.get_attr_term();
                        let next_name = info.iter_spec.of_trait.make_spec_attr_name("Next");
                        let term = format!("({attr_term}).({next_name})");
                        return Some(term);
                    },
                    "IterInv" => {
                        let attr_term = info.iter_spec.get_attr_term();
                        let next_name = info.iter_spec.of_trait.make_spec_attr_name("Inv");
                        let term = format!("({attr_term}).({next_name})");
                        return Some(term);
                    },
                    _ => (),
                }
            }
        }
        self.scope.lookup_literal(path)
    }
}

pub(crate) struct VerboseLoopAttrParser<'def, 'a, T> {
    locals: Vec<(mir::Local, String, code::LocalKind, bool, specs::Type<'def>)>,
    info: LoopMetaInfo<'def, 'a, T>,
}

impl<'def, 'a, T: ParamLookup<'def>> VerboseLoopAttrParser<'def, 'a, T> {
    pub(crate) const fn new(
        locals: Vec<(mir::Local, String, code::LocalKind, bool, specs::Type<'def>)>,
        scope: &'a T,
        iterator_info: Option<LoopIteratorInfo<'def>>,
    ) -> Self {
        let info = LoopMetaInfo {
            scope,
            iterator_info,
        };
        Self { locals, info }
    }
}

impl<'def, T: ParamLookup<'def>> LoopAttrParser for VerboseLoopAttrParser<'def, '_, T> {
    fn parse_loop_attrs<'b>(&'b mut self, attrs: &'b [&'b hir::AttrItem]) -> Result<specs::LoopSpec, String> {
        let mut invariant: Vec<coq::iris::IProp> = Vec::new();
        let mut inv_vars: Vec<InvVar> = Vec::new();
        let mut inv_var_set: HashSet<String> = HashSet::new();
        let mut existentials: Vec<coq::binder::Binder> = Vec::new();

        let mut params: Vec<coq::binder::Binder> = Vec::new();

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));

            match seg.as_str() {
                "params" => {
                    let p = RRParams::parse(&buffer, &self.info).map_err(str_err)?;
                    for param in p.params {
                        params.push(param.into());
                    }
                },
                "exists" => {
                    let params = RRParams::parse(&buffer, &self.info).map_err(str_err)?;
                    for param in params.params {
                        existentials.push(param.into());
                    }
                },
                "inv" | "invariant" => {
                    let parsed_iprop: MetaIProp = buffer.parse(&self.info).map_err(str_err)?;
                    invariant.push(parsed_iprop.into());
                },
                "inv_var" => {
                    let parsed_inv_var: InvVar = buffer.parse(&self.info).map_err(str_err)?;
                    inv_var_set.insert(parsed_inv_var.local.clone());
                    inv_vars.push(parsed_inv_var);
                },
                "inv_vars" => {
                    let params: parse::Punctuated<InvVar, MToken![,]> =
                        parse::Punctuated::<_, _>::parse_terminated(&buffer, &self.info).map_err(str_err)?;
                    for x in params {
                        inv_var_set.insert(x.local.clone());
                        inv_vars.push(x);
                    }
                },
                "ignore" => {
                    // ignore, this is the spec closure annotation
                },
                _ => {
                    return Err(format!("unknown attribute for loop specification: {:?}", args));
                },
            }
        }

        // now assemble the actual invariant
        // we split the local variables into three sets:
        // - named and definitely initialized variables, which we can use in the invariant
        // - named and maybe uninitialized variables, which we can not use in the invariant. Their type is
        //   preserved across the loop.
        // - compiler temporaries, which are required to be uninitialized. (NOTE: if we have mutable
        //   references around, this means that we need to extract observations and properly use their
        //   equalities)

        // binders that the invariant is parametric in
        let mut rfn_binder_names = BTreeMap::new();
        let mut rfn_binders = Vec::new();

        // proposition for unknown locals
        //let mut uninit_locals_prop: Vec<coq::iris::IProp> = Vec::new();

        // track locals
        let mut inv_locals: Vec<String> = Vec::new();
        let mut uninit_locals: Vec<String> = Vec::new();
        let mut preserved_locals: Vec<String> = Vec::new();

        let mut declare_iterator_var = None;

        // insert params at the front
        let param_name = "_params";
        let param_ident = coq::Ident::new(param_name);

        // get locals
        for (local, name, kind, initialized, ty) in &self.locals {
            // get the refinement type
            let mut rfn_ty = ty.get_rfn_type();
            //let ty_st: lang::SynType = ty.into();
            // wrap it in place_rfn, since we reason about places
            rfn_ty = model::Type::PlaceRfn(Box::new(rfn_ty)).into();

            // check if this the iterator variable
            let has_iterator_var = if let Some(iterator_info) = &self.info.iterator_info
                && iterator_info.iterator_variable == *local
            {
                true
            } else {
                false
            };

            let local_name = kind.mk_local_name(name);

            if *kind == code::LocalKind::CompilerTemp && !initialized {
                //let pred = format!("{local_name} ◁ₗ[π, Owned] .@ (◁ uninit {ty_st})");
                //uninit_locals_prop.push(coq::iris::IProp::Atom(pred));

                uninit_locals.push(name.clone());
            } else if *initialized && inv_var_set.contains(name) {
                inv_locals.push(name.clone());

                let binder_name = format!("_var_{name}");
                rfn_binder_names.insert(name, binder_name.clone());
                rfn_binders.push(coq::binder::Binder::new(Some(binder_name), rfn_ty));
            } else if *initialized && has_iterator_var {
                inv_locals.push(name.clone());
                declare_iterator_var = Some((name.clone(), local_name, rfn_ty.clone()));

                let binder_name = format!("_var_{name}");
                rfn_binder_names.insert(name, binder_name.clone());
                rfn_binders.push(coq::binder::Binder::new(Some(binder_name), rfn_ty));
            } else {
                preserved_locals.push(name.clone());
            }
        }
        // Important: order in `inv_locals` and `rfn_binders` needs to be the same!

        // add constraints on refinements
        let mut var_invariants = Vec::new();
        for inv_var in inv_vars {
            if let Some(binder_name) = rfn_binder_names.get(&inv_var.local) {
                if let Some(rfn) = &inv_var.rfn {
                    var_invariants.push(coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(format!(
                        "{binder_name} = {rfn}"
                    )))));
                } else {
                    // introduce an implicit quantifier and use xt
                    let ex_name = inv_var.local.clone();
                    existentials
                        .push(coq::binder::Binder::new(Some(ex_name.clone()), coq::term::RocqType::Infer));
                    var_invariants.push(coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(format!(
                        "{binder_name} = ($# {ex_name})"
                    )))));
                }
            } else {
                return Err(format!(
                    "Cannot specify loop invariant on potentially uninitialized variable {}",
                    inv_var.local
                ));
            }
        }

        // also add a constraint on the iterator variable
        let mut iterator_init_var = None;
        let mut param_binder_pos = 0;
        if let Some(iterator_info) = &self.info.iterator_info
            && let Some((name, _, rfn_ty)) = declare_iterator_var
            && let Some(binder_name) = rfn_binder_names.get(&name)
        {
            let ex_name = iterator_info.binder_name.clone();
            existentials.push(coq::binder::Binder::new(Some(ex_name.clone()), coq::term::RocqType::Infer));
            var_invariants.push(coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(format!(
                "{binder_name} = ($# {ex_name})"
            )))));

            let init_value_binder = format!("_init_{name}");
            let init_value_ty = coq::term::RocqType::UserDefined(model::Type::RTXT(Box::new(rfn_ty)));

            rfn_binders.insert(0, coq::binder::Binder::new(Some(init_value_binder.clone()), init_value_ty));
            param_binder_pos = 1;
            iterator_init_var = Some(name.clone());

            let iterator_param_name = "_iterator_param";

            // history
            existentials.push(coq::binder::Binder::new(
                Some(iterator_info.history_name.clone()),
                coq::term::RocqType::Infer,
            ));
            params
                .push(coq::binder::Binder::new(Some(iterator_param_name.to_owned()), coq::term::Type::Infer));

            var_invariants.push(coq::iris::IProp::Atom(format!(
                "IteratorNextFusedTrans ({}) π {iterator_param_name} {init_value_binder} {} {}",
                iterator_info.iter_spec.get_attr_term(),
                iterator_info.history_name,
                iterator_info.binder_name
            )));

            // invariant
            let attr_term = iterator_info.iter_spec.get_attr_term();
            let inv_name = iterator_info.iter_spec.of_trait.make_spec_attr_name("Inv");
            var_invariants.push(coq::iris::IProp::Atom(format!(
                "({attr_term}).({inv_name}) π {iterator_param_name} {}",
                iterator_info.binder_name
            )));
        }

        // prepare params and insert at the front, but after the optional initial iterator state
        let param_binders = coq::binder::BinderList::new(params);
        let (param_pat, param_ty) = param_binders.uncurry();
        rfn_binders.insert(param_binder_pos, coq::binder::Binder::new(Some(param_name.to_owned()), param_ty));

        var_invariants.extend(invariant);
        //var_invariants.extend(uninit_locals_prop);

        let prop_body = coq::iris::IProp::Sep(var_invariants);
        let prop_body =
            coq::iris::IProp::Exists(coq::binder::BinderList::new(existentials), Box::new(prop_body));

        let prop_body: coq::term::Term = coq::term::RocqTerm::AsType(
            Box::new(coq::term::RocqTerm::UserDefined(model::Term::IProp(prop_body))),
            Box::new(coq::term::RocqType::UserDefined(model::Type::IProp)),
        );
        let pat = format!("'{param_pat}");
        let prop_body = coq::term::RocqTerm::LetIn(
            pat,
            Box::new(coq::term::RocqTerm::Ident(param_ident)),
            Box::new(prop_body),
        );
        let pred =
            coq::term::RocqTerm::Lambda(coq::binder::BinderList::new(rfn_binders), Box::new(prop_body));

        Ok(specs::LoopSpec::new(pred, inv_locals, preserved_locals, uninit_locals, iterator_init_var))
    }
}
