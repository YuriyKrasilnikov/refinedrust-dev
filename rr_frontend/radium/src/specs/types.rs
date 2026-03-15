// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use derive_more::Constructor;

use crate::specs::{GenericScopeInst, traits};
use crate::{coq, lang};

#[derive(Clone, Eq, PartialEq, Debug, Constructor)]
pub struct AdtShimInfo {
    /// if this is an enum, its name
    enum_name: Option<String>,

    /// whether the type definition needs trait attributes
    needs_trait_attrs: bool,

    /// For atomic types: the inner field's [`SynType`] `Display` string.
    ///
    /// `None` for non-atomic types. When `Some`, the type has `mode(atomic)` and
    /// the string can be parsed back to determine the [`OpType`] and [`SynType`]
    /// for atomic operations (e.g. `"BoolSynType"`, `"(IntSynType U8)"`, `"PtrSynType"`).
    atomic_inner_st: Option<String>,
}

impl AdtShimInfo {
    #[must_use]
    pub const fn empty() -> Self {
        Self::new(None, false, None)
    }

    #[must_use]
    pub const fn enum_name(&self) -> Option<&String> {
        self.enum_name.as_ref()
    }

    #[must_use]
    // TODO: This field is currently unused
    pub const fn needs_trait_attrs(&self) -> bool {
        self.needs_trait_attrs
    }

    #[must_use]
    pub fn is_atomic(&self) -> bool {
        self.atomic_inner_st.is_some()
    }

    #[must_use]
    pub fn atomic_inner_st(&self) -> Option<&str> {
        self.atomic_inner_st.as_deref()
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Literal {
    /// Rust name
    pub rust_name: Option<String>,

    /// Rocq name of the type
    pub type_term: String,

    /// the refinement type
    pub refinement_type: coq::term::Type,

    /// the syntactic type
    pub syn_type: lang::SynType,

    /// extra info needed for using this literal
    pub info: AdtShimInfo,
}

pub type LiteralRef<'def> = &'def Literal;

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct LiteralUse<'def> {
    /// definition
    pub(crate) def: LiteralRef<'def>,

    /// parameters
    pub(crate) scope_inst: Option<GenericScopeInst<'def>>,
}

impl<'def> LiteralUse<'def> {
    #[must_use]
    pub const fn new(s: LiteralRef<'def>, scope_inst: GenericScopeInst<'def>) -> Self {
        LiteralUse {
            def: s,
            scope_inst: Some(scope_inst),
        }
    }

    #[must_use]
    pub const fn new_with_annot(s: LiteralRef<'def>) -> Self {
        LiteralUse {
            def: s,
            scope_inst: None,
        }
    }

    /// Get the refinement type of a struct usage.
    /// This requires that all type parameters of the struct have been instantiated.
    #[must_use]
    pub(crate) fn get_rfn_type(&self) -> String {
        let ty_inst: Vec<_> = self
            .scope_inst
            .as_ref()
            .unwrap_or(&GenericScopeInst::empty())
            .get_direct_ty_params_with_assocs()
            .into_iter()
            .map(|ty| ty.get_rfn_type())
            .collect();

        let rfn_type = self.def.refinement_type.to_string();
        let applied = coq::term::App::new(rfn_type, ty_inst);
        applied.to_string()
    }

    /// Get the `syn_type` term for this type use.
    #[must_use]
    pub fn generate_raw_syn_type_term(&self) -> lang::SynType {
        // For atomic transparent single-field types, the syn_type is already
        // the inner field's fully-determined SynType (e.g. PtrSynType).
        // Don't apply type params — the inner layout doesn't depend on them.
        if self.def.info.is_atomic() {
            return self.def.syn_type.clone();
        }
        let ty_inst: Vec<lang::SynType> = self
            .scope_inst
            .as_ref()
            .unwrap_or(&GenericScopeInst::empty())
            .get_direct_ty_params_with_assocs()
            .into_iter()
            .map(Into::into)
            .collect();
        let specialized_spec = coq::term::App::new(self.def.syn_type.clone(), ty_inst);
        lang::SynType::Literal(specialized_spec.to_string())
    }

    #[must_use]
    pub fn generate_syn_type_term(&self) -> lang::SynType {
        // For atomic transparent single-field types, the syn_type is already
        // the inner field's fully-determined SynType (e.g. PtrSynType).
        // Don't apply type params — the inner layout doesn't depend on them.
        if self.def.info.is_atomic() {
            return self.def.syn_type.clone();
        }
        let ty_inst: Vec<lang::SynType> = self
            .scope_inst
            .as_ref()
            .unwrap_or(&GenericScopeInst::empty())
            .get_direct_ty_params_with_assocs()
            .into_iter()
            .map(Into::into)
            .collect();
        let specialized_spec = coq::term::App::new(self.def.syn_type.clone(), ty_inst);
        lang::SynType::Literal(format!("({specialized_spec} : syn_type)"))
    }

    /// Generate a string representation of this type use.
    #[must_use]
    pub(crate) fn generate_type_term(&self) -> String {
        if let Some(scope_inst) = self.scope_inst.as_ref() {
            let rt_inst = scope_inst
                .get_all_ty_params_with_assocs()
                .iter()
                .map(|ty| format!("({})", ty.get_rfn_type()))
                .chain(
                    (if self.def.info.needs_trait_attrs {
                        scope_inst.get_direct_trait_requirements()
                    } else {
                        &[]
                    })
                    .iter()
                    .map(traits::ReqInst::get_attr_term),
                )
                .collect::<Vec<_>>()
                .join(" ");
            format!("({} {rt_inst} {})", self.def.type_term, scope_inst.instantiation(true, true))
        } else {
            self.def.type_term.clone()
        }
    }
}
