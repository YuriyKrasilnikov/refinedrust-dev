// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// Parsing of `RefinedRust` struct specifications.
use attribute_parse::{MToken, parse};
use log::info;
use parse::{Parse, Peek as _};
use radium::{coq, specs};
use rr_rustc_interface::hir;

use crate::spec_parsers::parse_utils::{
    IProp, IdentOrTerm, LiteralType, ParamLookup, RRCoqContextItem, RRParamsNamed, RRTerms, attr_args_tokens,
    str_err,
};

pub(crate) trait InvariantSpecParser {
    /// Parse attributes as an invariant type specification.
    /// `struct_name` is the name of the struct to generate.
    /// `params` are the type parameters of the surrounded type.
    ///
    /// Supported attributes on the invariant definition (outer):
    /// - `rr::refined_by`
    /// - `rr::exists`
    /// - `rr::invariant`
    /// - `rr::refines` for the inner refinement
    /// - `rr::context` for context items that are required to be available in the definition
    ///
    /// Returns whether a Boolean stating whether a `rr::refines` attribute was included.
    fn parse_invariant_spec<'a>(
        &'a mut self,
        struct_name: &str,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<(specs::invariants::Spec, bool), String>;
}

/// Parse a binder pattern with an optional Coq type annotation, e.g.
/// `"(x, y)" : "(Z * Z)%type"`
struct RfnPattern {
    rfn_pat: coq::binder::Pattern,
    rfn_type: Option<coq::term::Type>,
}

impl<'def, T: ParamLookup<'def>> Parse<T> for RfnPattern {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let pat = parse::LitStr::parse(stream, meta)?;
        let (pat, _) = meta.process_coq_literal(pat.value().as_str());

        // optionally, parse a type annotation (otherwise, let Coq inference do its thing)
        if parse::Colon::peek(stream) {
            stream.parse::<_, MToken![:]>(meta)?;
            let ty: parse::LitStr = stream.parse(meta)?;
            let (processed_rt, _) = meta.process_coq_literal(ty.value().as_str());

            Ok(Self {
                rfn_pat: pat,
                rfn_type: Some(coq::term::Type::Literal(processed_rt)),
            })
        } else {
            Ok(Self {
                rfn_pat: pat,
                rfn_type: None,
            })
        }
    }
}

/// Representation of the `IProps` that can appear in an invariant clause.
enum MetaIProp {
    /// `#[rr::invariant("..")]` or `#[rr::invariant("H" : "..")]`
    Pure(String, Option<String>),
    /// `#[rr::invariant(#iris "..")]`
    Iris(coq::iris::IProp),
    /// `#[rr::invariant(#type "l" : "rfn" @ "ty")]`
    Type(specs::TyOwnSpec),
    /// `#[rr::invariant(#own "...")]` (only for the Owned predicate)
    Own(coq::iris::IProp),
    /// `#[rr::invariant(#shr "...")]` (only for the Shared predicate)
    Shared(coq::iris::IProp),
}

impl<'def, T: ParamLookup<'def>> Parse<T> for MetaIProp {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        if parse::Pound::peek(stream) {
            stream.parse::<_, MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = stream.parse(meta)?;
            match macro_cmd.value().as_str() {
                "iris" => {
                    let prop: IProp = stream.parse(meta)?;
                    Ok(Self::Iris(prop.into()))
                },

                "own" => {
                    let prop: IProp = stream.parse(meta)?;
                    Ok(Self::Own(prop.into()))
                },

                "shr" => {
                    let prop: IProp = stream.parse(meta)?;
                    Ok(Self::Shared(prop.into()))
                },

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

                    let spec = specs::TyOwnSpec::new(loc_str, rfn_str, type_str, true, annot_meta);
                    Ok(Self::Type(spec))
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

#[derive(Copy, Clone)]
pub(crate) struct InvariantSpecFlags(specs::invariants::SpecFlags);

impl From<InvariantSpecFlags> for specs::invariants::SpecFlags {
    fn from(spec: InvariantSpecFlags) -> Self {
        spec.0
    }
}

/// Detect whether any `#[rr::mode(atomic)]` attribute is present.
/// Reuses `InvariantSpecFlags` parser for uniformity with `parse_invariant_spec`.
pub(crate) fn detect_atomic_mode(attrs: &[&hir::AttrItem]) -> bool {
    attrs.iter().any(|it| {
        it.path.segments.get(1).is_some_and(|seg| seg.as_str() == "mode") && {
            let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));
            // InvariantSpecFlags implements Parse<U> for any U — scope unused
            buffer
                .parse::<(), InvariantSpecFlags>(&())
                .is_ok_and(|f| specs::invariants::SpecFlags::from(f) == specs::invariants::SpecFlags::Atomic)
        }
    })
}

impl<U> Parse<U> for InvariantSpecFlags {
    fn parse(stream: parse::Stream<'_>, meta: &U) -> parse::Result<Self> {
        let mode: parse::Ident = stream.parse(meta)?;

        match mode.value().as_str() {
            "persistent" => Ok(Self(specs::invariants::SpecFlags::Persistent)),
            "plain" => Ok(Self(specs::invariants::SpecFlags::Plain)),
            "na" => Ok(Self(specs::invariants::SpecFlags::NonAtomic)),
            "atomic" => Ok(Self(specs::invariants::SpecFlags::Atomic)),
            _ => Err(parse::Error::OtherErr(stream.pos().unwrap(), "invalid ADT mode".to_owned())),
        }
    }
}

pub(crate) struct VerboseInvariantSpecParser<'a, T> {
    scope: &'a T,
}

impl<'a, 'def, T: ParamLookup<'def>> VerboseInvariantSpecParser<'a, T> {
    pub(crate) const fn new(scope: &'a T) -> Self {
        Self { scope }
    }
}

impl<'def, T: ParamLookup<'def>> InvariantSpecParser for VerboseInvariantSpecParser<'_, T> {
    fn parse_invariant_spec<'a>(
        &'a mut self,
        struct_name: &str,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<(specs::invariants::Spec, bool), String> {
        if attrs.is_empty() {
            return Err("no invariant specifications given".to_owned());
        }

        let mut invariants: Vec<(coq::iris::IProp, specs::invariants::Mode)> = Vec::new();
        let mut type_invariants: Vec<specs::TyOwnSpec> = Vec::new();
        let mut abstracted_refinement = None;

        let mut rfn_pat = "placeholder_pat".to_owned();
        let mut rfn_type = coq::term::Type::Infer;
        //let mut xt_type = coq::term::Type::Infer;

        let mut existentials: Vec<coq::binder::Binder> = Vec::new();

        // use Plain as the default
        let mut inv_flags = specs::invariants::SpecFlags::Plain;

        let mut params: Vec<coq::binder::Binder> = Vec::new();

        let mut ty_lfts = Vec::new();
        let mut ty_wf_elctx = Vec::new();

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(args));
            match seg.as_str() {
                "refined_by" => {
                    let pat = RfnPattern::parse(&buffer, self.scope).map_err(str_err)?;

                    rfn_pat = pat.rfn_pat;

                    if let Some(ty) = pat.rfn_type {
                        rfn_type = ty;
                    }
                    //if let Some(ty) = pat.xt_type {
                    //xt_type = ty;
                    //}
                },
                "inv" | "invariant" => {
                    let prop = MetaIProp::parse(&buffer, self.scope).map_err(str_err)?;

                    match prop {
                        MetaIProp::Own(iprop) => {
                            invariants.push((iprop, specs::invariants::Mode::OnlyOwned));
                        },
                        MetaIProp::Shared(iprop) => {
                            invariants.push((iprop, specs::invariants::Mode::OnlyShared));
                        },
                        MetaIProp::Iris(iprop) => {
                            invariants.push((iprop, specs::invariants::Mode::All));
                        },
                        MetaIProp::Type(ty) => {
                            type_invariants.push(ty);
                        },
                        MetaIProp::Pure(p, name) => match name {
                            None => {
                                invariants.push((
                                    coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(p))),
                                    specs::invariants::Mode::All,
                                ));
                            },
                            Some(n) => {
                                invariants.push((
                                    coq::iris::IProp::Pure(Box::new(coq::term::Term::UserDefined(
                                        radium::model::Term::WithName(
                                            Box::new(coq::term::Term::Literal(p)),
                                            n,
                                        ),
                                    ))),
                                    specs::invariants::Mode::All,
                                ));
                            },
                        },
                    }
                },
                "ty_lfts" => {
                    let mut terms = RRTerms::parse(&buffer, self.scope).map_err(str_err)?;
                    ty_lfts.append(&mut terms.terms);
                },
                "ty_wf_elctx" | "ty_wf_E" => {
                    let mut terms = RRTerms::parse(&buffer, self.scope).map_err(str_err)?;
                    ty_wf_elctx.append(&mut terms.terms);
                },
                "exists" => {
                    let params = RRParamsNamed::parse(&buffer, self.scope).map_err(str_err)?;
                    existentials.append(&mut params.params.into_iter().map(Into::into).collect());
                },
                "mode" => {
                    let mode = InvariantSpecFlags::parse(&buffer, self.scope).map_err(str_err)?;

                    inv_flags = mode.into();
                },
                "refines" => {
                    let term = IdentOrTerm::parse(&buffer, self.scope).map_err(str_err)?;

                    if abstracted_refinement.is_some() {
                        return Err("multiple refines specifications given".to_owned());
                    }
                    abstracted_refinement = Some(term.to_string());
                },
                "context" => {
                    let param = RRCoqContextItem::parse(&buffer, self.scope).map_err(str_err)?;

                    params.push(coq::binder::Binder::new_generalized(
                        coq::binder::Kind::MaxImplicit,
                        None,
                        coq::term::Type::Literal(param.item),
                    ));
                },
                _ => {
                    //skip, this may be part of an enum spec
                },
            }
        }

        let refinement_included = abstracted_refinement.is_some();

        //let xt_injection = format!("(@xmap ({xt_type}) ({rfn_type}) _)");

        let spec = specs::invariants::Spec::new(
            struct_name.to_owned(),
            inv_flags,
            rfn_type,
            //xt_type,
            //xt_injection,
            rfn_pat,
            existentials,
            invariants,
            type_invariants,
            ty_lfts,
            ty_wf_elctx,
            abstracted_refinement,
            params,
        );

        Ok((spec, refinement_included))
    }
}

/// A parsed specification for a field.
pub(crate) struct StructFieldSpec<'def> {
    /// the (default or annotated) type of the field
    pub ty: specs::Type<'def>,
    /// optional refinement specified here
    pub rfn: Option<String>,
}

pub(crate) trait StructFieldSpecParser<'def> {
    /// Parse attributes on a struct field as a type specification.
    /// Supported attributes:
    /// - `rr::field(r)`
    /// - `rr::field(r @ type)`
    fn parse_field_spec<'a>(
        &'a mut self,
        field_name: &str,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<StructFieldSpec<'def>, String>;
}

/// Parses attributes on a field to a `StructFieldSpec`, using a given default type for the field
/// in case none is annotated.
pub(crate) struct VerboseStructFieldSpecParser<'a, 'def, T, F>
where
    F: Fn(specs::types::Literal) -> specs::types::LiteralRef<'def>,
{
    /// The translated Rust field type that is used as a default.
    field_type: &'a specs::Type<'def>,

    /// the type parameters of this struct
    scope: &'a T,

    /// whether to expect a refinement to be specified or not
    expect_rfn: bool,

    make_literal: F,
    //ty_scope: &'a [Option<specs::Type<'def>>],
    //rfnty_scope: &'a [Option<coq::term::Type>],
}

impl<'a, 'def, T: ParamLookup<'def>, F> VerboseStructFieldSpecParser<'a, 'def, T, F>
where
    F: Fn(specs::types::Literal) -> specs::types::LiteralRef<'def>,
{
    pub(crate) const fn new(
        field_type: &'a specs::Type<'def>,
        scope: &'a T,
        expect_rfn: bool,
        make_literal: F,
    ) -> Self {
        Self {
            field_type,
            scope,
            expect_rfn,
            make_literal,
        }
    }

    fn make_type(&self, lit: &LiteralType, ty: &specs::Type<'def>) -> specs::Type<'def> {
        // literal type given, we use this literal type as the RR semantic type
        // just use the syntype from the Rust type

        // TODO: get CoqType for refinement.
        // maybe have it as an annotation? the Infer is currently a placeholder.
        // we need this in order to be able to specify the invariant spec separately.

        info!("making type: {:?}, {:?}", lit, ty);
        let lit_ty = specs::types::Literal {
            rust_name: None,
            type_term: lit.ty.clone(),
            refinement_type: coq::term::Type::Infer,
            syn_type: ty.into(),
            info: specs::types::AdtShimInfo::empty(),
        };
        let lit_ref = (self.make_literal)(lit_ty);
        let lit_use = specs::types::LiteralUse::new_with_annot(lit_ref);

        specs::Type::Literal(lit_use)
    }
}

impl<'def, T: ParamLookup<'def>, F> StructFieldSpecParser<'def>
    for VerboseStructFieldSpecParser<'_, 'def, T, F>
where
    F: Fn(specs::types::Literal) -> specs::types::LiteralRef<'def>,
{
    fn parse_field_spec(
        &mut self,
        field_name: &str,
        attrs: &[&hir::AttrItem],
    ) -> Result<StructFieldSpec<'def>, String> {
        info!("parsing attributes of field {:?}: {:?}", field_name, attrs);

        let mut field_type = None;
        let mut parsed_rfn = None;

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(args));

            if seg.as_str() != "field" {
                return Err(format!("unknown attribute for struct field specification: {:?}", args));
            }

            if self.expect_rfn {
                let rfn: parse::LitStr = buffer.parse(self.scope).map_err(str_err)?;
                let (rfn, _) = self.scope.process_coq_literal(rfn.value().as_str());
                parsed_rfn = Some(rfn);

                if parse::At::peek(&buffer) {
                    info!("expecting type");
                    buffer.parse::<_, MToken![@]>(self.scope).map_err(str_err)?;
                } else {
                    continue;
                }
            }

            let ty = LiteralType::parse(&buffer, self.scope).map_err(str_err)?;

            if field_type.is_some() {
                return Err(format!("field attribute specified twice for field {:?}", field_name));
            }

            field_type = Some(self.make_type(&ty, self.field_type));
        }

        let ty = match field_type {
            Some(ty) => ty,
            None => self.field_type.clone(),
        };

        Ok(StructFieldSpec {
            ty,
            rfn: parsed_rfn,
        })
    }
}
