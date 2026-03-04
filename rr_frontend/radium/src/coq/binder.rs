//! The [implicit arguments], and [binders].
//!
//! [implicit arguments]: https://rocq-prover.org/doc/v8.20/refman/language/extensions/implicit-arguments.html#implicit-arguments
//! [binders]: https://rocq-prover.org/doc/v8.20/refman/language/core/assumptions.html#binders

use std::fmt;

use derive_more::Display;

use crate::coq::term;
use crate::{fmt_list, model};

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Kind {
    /// `()`
    Explicit,

    /// `{}`
    MaxImplicit,

    /// `[]`
    NonMaxImplicit,
}

/// A [binder].
///
/// [binder]: https://rocq-prover.org/doc/v8.20/refman/language/core/assumptions.html#grammar-token-binder
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Display)]
pub enum Binder {
    #[display("({}: {})", self.get_name(), _1)]
    Default(Option<String>, term::Type),

    #[display("{}", _0)]
    Implicit(Implicit),

    #[display("{}", _0)]
    Generalizing(Generalizing),
}

impl Binder {
    #[must_use]
    pub fn new<I: Into<term::Type>>(name: Option<String>, ty: I) -> Self {
        Self::Default(name, ty.into())
    }

    #[must_use]
    pub fn new_with_name_hint<I: Into<term::Type>>(name: String, ty: I) -> Self {
        let ty = ty.into();
        let ty = model::Type::WithName(Box::new(term::RocqTerm::Type(Box::new(ty))), name.clone());
        Self::Default(Some(name), term::RocqType::UserDefined(ty))
    }

    #[must_use]
    pub const fn new_implicit(kind: Kind, name: Option<String>, ty: Option<term::Type>) -> Self {
        Self::Implicit(Implicit { kind, name, ty })
    }

    #[must_use]
    pub const fn new_generalized(kind: Kind, name: Option<String>, term: term::Type) -> Self {
        Self::Generalizing(Generalizing {
            kind,
            name,
            ty: term,
        })
    }

    #[must_use]
    pub fn new_rrgs() -> Self {
        Self::new_generalized(
            Kind::MaxImplicit,
            Some("RRGS".to_owned()),
            term::Type::Literal("refinedrustGS Σ".to_owned()),
        )
    }

    #[must_use]
    pub fn get_name(&self) -> String {
        match self {
            Self::Default(name, _) => name.clone().unwrap_or_else(|| "_".to_owned()),
            Self::Implicit(i) => i.name.clone().unwrap_or_else(|| "_".to_owned()),
            Self::Generalizing(g) => g.name.clone().unwrap_or_else(|| "_".to_owned()),
        }
    }

    #[must_use]
    #[expect(clippy::ref_option)]
    pub const fn get_name_ref(&self) -> &Option<String> {
        match self {
            Self::Default(name, _) => name,
            Self::Implicit(i) => &i.name,
            Self::Generalizing(g) => &g.name,
        }
    }

    #[must_use]
    pub const fn get_type(&self) -> Option<&term::Type> {
        match self {
            Self::Default(_, ty) => Some(ty),
            Self::Implicit(i) => i.ty.as_ref(),
            Self::Generalizing(g) => Some(&g.ty),
        }
    }

    #[must_use]
    pub(crate) const fn is_implicit(&self) -> bool {
        matches!(self, Self::Generalizing(_))
    }

    #[must_use]
    pub(crate) fn is_dependent_on_sigma(&self) -> bool {
        let Some(term::Type::Literal(lit)) = self.get_type() else {
            return false;
        };

        lit.contains('Σ')
    }

    #[must_use]
    pub fn set_name(self, name: String) -> Self {
        match self {
            Self::Default(_, ty) => Self::Default(Some(name), ty),
            Self::Implicit(i) => Self::Implicit(Implicit {
                name: Some(name),
                ..i
            }),
            Self::Generalizing(g) => Self::Generalizing(Generalizing {
                name: Some(name),
                ..g
            }),
        }
    }

    pub fn make_implicit(&mut self, kind: Kind) {
        match self {
            Self::Default(name, term) => {
                *self = Self::Generalizing(Generalizing {
                    kind,
                    name: name.clone(),
                    ty: term.clone(),
                });
            },
            Self::Generalizing(g) => {
                g.kind = kind;
            },
            Self::Implicit(i) => {
                i.kind = kind;
            },
        }
    }
}

/// [Implicit argument] binders.
///
/// [Implicit argument]: https://rocq-prover.org/doc/v8.20/refman/language/extensions/implicit-arguments.html#grammar-token-implicit_binders
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Implicit {
    kind: Kind,
    name: Option<String>,
    ty: Option<term::Type>,
}

impl fmt::Display for Implicit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = match (&self.name, &self.ty) {
            (Some(name), Some(ty)) => format!("{} : {}", name, ty),
            (Some(name), None) => name.to_owned(),
            (None, Some(ty)) => ty.to_string(),
            (None, None) => String::new(),
        };

        match &self.kind {
            Kind::Explicit => panic!("Implicit argument binders cannot have Kind::Explicit"),
            Kind::MaxImplicit => write!(f, "{{{}}}", inner),
            Kind::NonMaxImplicit => write!(f, "[{}]", inner),
        }
    }
}

/// [Implicit generalization] binders.
///
/// [Implicit generalization]: https://rocq-prover.org/doc/v8.20/refman/language/extensions/implicit-arguments.html#grammar-token-generalizing_binder
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Generalizing {
    kind: Kind,
    name: Option<String>,
    ty: term::Type,
}

impl fmt::Display for Generalizing {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = match &self.name {
            Some(name) => format!("{} : !{}", name, self.ty),
            None => format!("!{}", self.ty),
        };

        match &self.kind {
            Kind::Explicit => write!(f, "`({})", inner),
            Kind::MaxImplicit => write!(f, "`{{{}}}", inner),
            Kind::NonMaxImplicit => write!(f, "`[{}]", inner),
        }
    }
}

/// A Rocq pattern, e.g., "x" or "'(x, y)".
pub type Pattern = String;

#[expect(clippy::module_name_repetitions)]
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Display)]
#[display("{}", fmt_list!(_0, " "))]
pub struct BinderList(pub Vec<Binder>);

impl BinderList {
    #[must_use]
    pub const fn new(params: Vec<Binder>) -> Self {
        Self(params)
    }

    #[must_use]
    pub const fn empty() -> Self {
        Self(vec![])
    }

    pub fn make_implicit(&mut self, kind: Kind) {
        for x in &mut self.0 {
            x.make_implicit(kind);
        }
    }

    pub fn append(&mut self, params: Vec<Binder>) {
        self.0.extend(params);
    }

    /// Make using terms for this list of binders
    #[must_use]
    pub fn make_using_terms(&self) -> Vec<term::Term> {
        self.0
            .iter()
            .filter_map(|x| if x.is_implicit() { None } else { Some(term::Term::Literal(x.get_name())) })
            .collect()
    }

    /// Make terms implicit instantiation terms `(a := a)` for this list of binders
    #[must_use]
    pub fn make_implicit_inst_terms(&self) -> Vec<term::Term> {
        self.0
            .iter()
            .map(|x| term::Term::Literal(format!("({} := {})", x.get_name(), x.get_name())))
            .collect()
    }

    #[must_use]
    pub fn uncurry(&self) -> (Pattern, term::Type) {
        if self.0.is_empty() {
            return ("_".to_owned(), term::Type::Unit);
        }

        let mut pattern = String::with_capacity(100);
        let mut types = String::with_capacity(100);

        pattern.push('(');
        types.push('(');

        let mut need_sep = false;
        for binder in &self.0 {
            if need_sep {
                pattern.push_str(", ");
                types.push_str(" * ");
            }

            pattern.push_str(&binder.get_name());
            types.push_str(&format!("{}", binder.get_type().unwrap()));

            need_sep = true;
        }

        pattern.push(')');
        types.push(')');

        (pattern, term::Type::Literal(types))
    }
}
