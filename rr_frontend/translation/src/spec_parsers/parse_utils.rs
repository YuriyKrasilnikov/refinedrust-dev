// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::fmt;
use std::sync::LazyLock;

use attribute_parse::{MToken, parse};
use derive_more::Display;
use log::trace;
use parse::Peek as _;
use radium::{coq, specs};
use regex::{Captures, Regex};
/// This provides some general utilities for RefinedRust-specific attribute parsing.
use rr_rustc_interface::{ast, hir};

pub(crate) fn attr_args_tokens(x: &hir::AttrArgs) -> ast::tokenstream::TokenStream {
    match x {
        hir::AttrArgs::Delimited(args) => flatten_invisible_groups(&args.tokens),
        hir::AttrArgs::Empty | hir::AttrArgs::Eq { .. } => ast::tokenstream::TokenStream::default(),
    }
}

/// Recursively removes `Delimiter::Invisible` groups from a token stream,
/// splicing their contents in place. Macro expansions wrap `$($tt:tt)*`
/// fragments in invisible groups, which the attribute parsers cannot handle.
fn flatten_invisible_groups(stream: &ast::tokenstream::TokenStream) -> ast::tokenstream::TokenStream {
    use ast::token::Delimiter;
    use ast::tokenstream::TokenTree;

    let mut out = Vec::new();
    for tt in stream.iter() {
        match tt {
            TokenTree::Delimited(_, _, Delimiter::Invisible(_), inner) => {
                // Splice the inner tokens, recursively flattening nested groups.
                for inner_tt in flatten_invisible_groups(inner).iter() {
                    out.push(inner_tt.clone());
                }
            }
            TokenTree::Delimited(span, spacing, delim, inner) => {
                // Preserve real delimiters (parens, braces, brackets) but
                // flatten any invisible groups inside them.
                out.push(TokenTree::Delimited(*span, *spacing, *delim, flatten_invisible_groups(inner)));
            }
            other => out.push(other.clone()),
        }
    }
    ast::tokenstream::TokenStream::new(out)
}

/// Parse either a literal string (a term/pattern) or an identifier, e.g.
/// `x`, `z`, `"w"`, `"(a, b)"`
#[derive(Debug)]
pub(crate) enum IdentOrTerm {
    Ident(String),
    Term(String),
}

impl IdentOrTerm {
    fn process<'def, T: ParamLookup<'def>>(self, meta: &T) -> Self {
        match self {
            Self::Ident(id) => Self::Ident(id),
            Self::Term(t) => {
                let (s, _) = meta.process_coq_literal(&t);
                Self::Term(s)
            },
        }
    }
}

impl<U> parse::Parse<U> for IdentOrTerm
where
    U: ?Sized,
{
    fn parse(stream: parse::Stream<'_>, meta: &U) -> parse::Result<Self> {
        if let Ok(ident) = parse::Ident::parse(stream, meta) {
            // it's an identifer
            Ok(Self::Ident(ident.value()))
        } else {
            parse::LitStr::parse(stream, meta).map(|s| Self::Term(s.value()))
        }
    }
}

impl fmt::Display for IdentOrTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ident(s) | Self::Term(s) => write!(f, "{s}"),
        }
    }
}

/// Parse a refinement with an optional type annotation, e.g.
/// `x`, `"y"`, `x @ "int i32"`, `"(a, b)" @ "struct_t ...."`.
#[derive(Debug)]
pub(crate) struct LiteralTypeWithRef {
    pub rfn: IdentOrTerm,
    pub ty: Option<String>,
    pub raw: specs::structs::TypeIsRaw,
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for LiteralTypeWithRef {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        // check if a #raw annotation is present
        let loc = stream.pos();
        let mut raw = specs::structs::TypeIsRaw::No;
        if parse::Pound::peek(stream) {
            stream.parse::<_, MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = stream.parse(meta)?;
            match macro_cmd.value().as_str() {
                "raw" => {
                    raw = specs::structs::TypeIsRaw::Yes;
                },
                _ => return Err(parse::Error::OtherErr(loc.unwrap(), "Unsupported flag".to_owned())),
            }
        }

        // refinement
        let rfn: IdentOrTerm = stream.parse(meta)?;
        let rfn = rfn.process(meta);

        // optionally, parse a type annotation (otherwise, use the translated Rust type)
        if parse::At::peek(stream) {
            stream.parse::<_, MToken![@]>(meta)?;
            let ty: parse::LitStr = stream.parse(meta)?;
            let (ty, _) = meta.process_coq_literal(&ty.value());

            Ok(Self {
                rfn,
                ty: Some(ty),
                raw,
            })
        } else {
            Ok(Self { rfn, ty: None, raw })
        }
    }
}

/// Parse a type annotation.
#[derive(Debug)]
pub(crate) struct LiteralType {
    pub ty: String,
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for LiteralType {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let ty: parse::LitStr = stream.parse(meta)?;
        let (ty, _) = meta.process_coq_literal(&ty.value());

        Ok(Self { ty })
    }
}

pub(crate) struct IProp(coq::iris::IProp);

impl From<IProp> for coq::iris::IProp {
    fn from(iprop: IProp) -> Self {
        iprop.0
    }
}

/// Parse an iProp string, e.g. `"P ∗ Q ∨ R"`
impl<'def, T: ParamLookup<'def>> parse::Parse<T> for IProp {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let lit: parse::LitStr = stream.parse(meta)?;
        let (lit, _) = meta.process_coq_literal(&lit.value());

        Ok(Self(coq::iris::IProp::Atom(lit)))
    }
}

/// Parse a Coq type.
pub(crate) struct RRCoqType {
    pub ty: coq::term::Type,
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for RRCoqType {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let ty: parse::LitStr = stream.parse(meta)?;
        let (ty, _) = meta.process_coq_literal(&ty.value());
        let ty = coq::term::Type::Literal(ty);
        Ok(Self { ty })
    }
}

// A literal term.
#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) struct RRTerm {
    pub term: String,
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for RRTerm {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let term: parse::LitStr = stream.parse(meta)?;
        let (term, _) = meta.process_coq_literal(&term.value());
        Ok(Self { term })
    }
}
#[derive(Debug)]
pub(crate) struct RRTerms {
    pub(crate) terms: Vec<String>,
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for RRTerms {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let terms: parse::Punctuated<RRTerm, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(stream, meta)?;
        Ok(Self {
            terms: terms.into_iter().map(|x| x.term).collect(),
        })
    }
}

/// Parse a binder declaration with an optional Coq type annotation, e.g.
/// `x : "Z"`,
/// `"y"`,
/// `z`,
/// `w : "(Z * Z)%type"`
#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) struct RRParam(pub(crate) coq::binder::Binder);

impl From<RRParam> for coq::binder::Binder {
    fn from(param: RRParam) -> Self {
        param.0
    }
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for RRParam {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let name: IdentOrTerm = stream.parse(meta)?;
        let name = name.to_string();

        if parse::Colon::peek(stream) {
            stream.parse::<_, MToken![:]>(meta)?;
            let ty: RRCoqType = stream.parse(meta)?;
            Ok(Self(coq::binder::Binder::new(Some(name), ty.ty)))
        } else {
            Ok(Self(coq::binder::Binder::new(Some(name), coq::term::Type::Infer)))
        }
    }
}

/// Parse a list of comma-separated parameter declarations.
#[derive(Debug)]
pub(crate) struct RRParams {
    pub(crate) params: Vec<RRParam>,
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for RRParams {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let params: parse::Punctuated<RRParam, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(stream, meta)?;
        Ok(Self {
            params: params.into_iter().collect(),
        })
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) struct RRParamNamed(pub(crate) coq::binder::Binder);

impl From<RRParamNamed> for coq::binder::Binder {
    fn from(param: RRParamNamed) -> Self {
        param.0
    }
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for RRParamNamed {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let name: IdentOrTerm = stream.parse(meta)?;
        let name = name.to_string();

        if parse::Colon::peek(stream) {
            stream.parse::<_, MToken![:]>(meta)?;
            let ty: RRCoqType = stream.parse(meta)?;
            Ok(Self(coq::binder::Binder::new_with_name_hint(name, ty.ty)))
        } else {
            Ok(Self(coq::binder::Binder::new_with_name_hint(name, coq::term::Type::Infer)))
        }
    }
}
#[derive(Debug)]
pub(crate) struct RRParamsNamed {
    pub(crate) params: Vec<RRParamNamed>,
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for RRParamsNamed {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let params: parse::Punctuated<RRParamNamed, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(stream, meta)?;
        Ok(Self {
            params: params.into_iter().collect(),
        })
    }
}

pub(crate) struct CoqExportModule(coq::module::Export);

impl From<CoqExportModule> for coq::module::Export {
    fn from(path: CoqExportModule) -> Self {
        path.0
    }
}

/// Parse a `CoqModule`.
impl<U> parse::Parse<U> for CoqExportModule {
    fn parse(stream: parse::Stream<'_>, meta: &U) -> parse::Result<Self> {
        let path_or_module: parse::LitStr = stream.parse(meta)?;
        let path_or_module = path_or_module.value();

        if parse::Comma::peek(stream) {
            stream.parse::<_, MToken![,]>(meta)?;
            let module: parse::LitStr = stream.parse(meta)?;
            let module = module.value();

            Ok(Self(coq::module::Export::new(vec![module]).from(vec![path_or_module])))
        } else {
            Ok(Self(coq::module::Export::new(vec![path_or_module])))
        }
    }
}

/// Parse an assumed Coq context item, e.g.
/// ``"`{ghost_mapG Σ Z Z}"``.
#[derive(Debug)]
pub(crate) struct RRCoqContextItem {
    pub item: String,
    /// true if this should be put at the end of the dependency list, e.g. if it depends on type
    /// parameters
    pub at_end: bool,
}
impl<'def, T: ParamLookup<'def>> parse::Parse<T> for RRCoqContextItem {
    fn parse(stream: parse::Stream<'_>, meta: &T) -> parse::Result<Self> {
        let item: parse::LitStr = stream.parse(meta)?;
        let (item_str, annot_meta) = meta.process_coq_literal(&item.value());

        let at_end = !annot_meta.is_empty();

        //annot_meta.
        Ok(Self {
            item: item_str,
            at_end,
        })
    }
}
impl From<RRCoqContextItem> for coq::binder::Binder {
    fn from(x: RRCoqContextItem) -> Self {
        Self::new_generalized(coq::binder::Kind::MaxImplicit, None, coq::term::Type::Literal(x.item))
    }
}

#[expect(clippy::needless_pass_by_value)]
pub(crate) fn str_err(e: parse::Error) -> String {
    format!("{:?}", e)
}

/// Handle escape sequences in the given string.
fn handle_escapes(s: &str) -> String {
    String::from(s).replace("\\\"", "\"")
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub(crate) enum RustPathElem {
    AssocItem(String),
}

pub(crate) type RustPath = Vec<RustPathElem>;

#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Display)]
pub(crate) enum Projection {
    #[display("deref")]
    Deref,
    #[display("{}", _0)]
    Field(String),
}
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Projections(pub(crate) Vec<Projection>);
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct RustPlace {
    pub(crate) base: String,
    pub(crate) proj: Projections,
}

impl fmt::Display for Projections {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut needs_sep = false;
        for x in &self.0 {
            if needs_sep {
                write!(f, "_")?;
            }
            needs_sep = true;
            write!(f, "{x}")?;
        }

        Ok(())
    }
}

/// Lookup of lifetime and type parameters given their Rust source names.
pub(crate) trait ParamLookup<'def> {
    fn lookup_ty_param(&self, path: &RustPath) -> Option<specs::Type<'def>>;
    fn lookup_lft(&self, lft: &str) -> Option<&specs::LftParam>;
    fn lookup_literal(&self, path: &RustPath) -> Option<String>;

    fn lookup_place(&self, _place: &RustPlace, _modifier: Option<String>) -> Option<String> {
        None
    }

    /// Processes a literal Coq term annotated via an attribute.
    /// In particular, processes escapes `{...}` and replaces them via their interpretation, see
    /// below for supported escape sequences.
    ///
    /// Supported interpretations:
    /// - `{{...}}` is replaced by `{...}`
    /// - `{ty_of T}` is replaced by the type for the type parameter `T`
    /// - `{rt_of T}` is replaced by the refinement type of the type parameter `T`
    /// - `{xt_of T}` is replaced by the xt type of the type parameter `T`
    /// - `{st_of T}` is replaced by the syntactic type of the type parameter `T`
    /// - `{ly_of T}` is replaced by a term giving the layout of the type parameter `T`'s syntactic type
    /// - `{'a}` is replaced by a term corresponding to the lifetime parameter 'a
    ///
    /// We return the list of escaped types we depend on in order to properly track dependencies on
    /// variables.
    /// (This is needed for computing the lifetime constraints of invariant types)
    fn process_coq_literal(&self, s: &str) -> (String, specs::TypeAnnotMeta) {
        self.process_coq_literal_xt(s, false)
    }

    fn process_coq_literal_xt(&self, s: &str, rt_is_xt: bool) -> (String, specs::TypeAnnotMeta) {
        // compile these just once, not for every invocation of the method
        static IDENTCHARR: &str = "[_[[:alpha:]]]";
        // Note: the leading regex ([^{]|^) is supposed to rule out leading {, for the RE_LIT rule.
        static PREFIXR: &str = "([^{]|^)";
        static IDENTR: LazyLock<String> = LazyLock::new(|| format!("{IDENTCHARR}[0-9{IDENTCHARR}]*"));
        static PLACER: LazyLock<String> = LazyLock::new(|| format!("[0-9{IDENTCHARR}.\\*()]"));
        static PATHR: LazyLock<String> = LazyLock::new(|| format!("(({}::)*)({})", *IDENTR, *IDENTR));
        static RE_RT_OF: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(&format!(r"{PREFIXR}\{{\s*rt_of\s+{}\s*\}}", *PATHR)).unwrap());
        static RE_ST_OF: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(&format!(r"{PREFIXR}\{{\s*st_of\s+{}\s*\}}", *PATHR)).unwrap());
        static RE_LY_OF: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(&format!(r"{PREFIXR}\{{\s*ly_of\s+{}\s*\}}", *PATHR)).unwrap());
        static RE_TY_OF: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(&format!(r"{PREFIXR}\{{\s*ty_of\s+{}\s*\}}", *PATHR)).unwrap());
        static RE_XT_OF: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(&format!(r"{PREFIXR}\{{\s*xt_of\s+{}\s*\}}", *PATHR)).unwrap());
        static RE_LFT_OF: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(&format!(r"{PREFIXR}\{{\s*'({})\s*\}}", *IDENTR)).unwrap());
        static RE_LIT: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(&format!(r"{PREFIXR}\{{\s*{}\s*\}}", *PATHR)).unwrap());
        static RE_PLACE: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(&format!(r"{PREFIXR}\{{\s*({}*)\s*\}}", *PLACER)).unwrap());

        // Parse a path to an item.
        fn parse_path(prefix: Option<regex::Match<'_>>) -> RustPath {
            let mut path = Vec::new();
            if let Some(prefix) = prefix {
                let prefix = prefix.as_str();
                for seg in prefix.split("::") {
                    if !seg.is_empty() {
                        path.push(RustPathElem::AssocItem(seg.to_owned()));
                    }
                }
            }
            path
        }

        let mut annot_meta = specs::TypeAnnotMeta::empty();

        let s = handle_escapes(s);

        let cs = &s;
        let cs = RE_RT_OF.replace_all(cs, |c: &Captures<'_>| {
            let mut path = parse_path(c.get(2));

            path.push(RustPathElem::AssocItem(c[4].to_string()));

            let param = self.lookup_ty_param(&path);

            let Some(param) = param else {
                return "ERR".to_owned();
            };

            annot_meta.add_type(&param);
            if rt_is_xt {
                format!("{}(RT_xt {})", &c[1], &param.get_rfn_type())
            } else {
                format!("{}{}", &c[1], &param.get_rfn_type())
            }
        });

        let cs = RE_XT_OF.replace_all(&cs, |c: &Captures<'_>| {
            let mut path = parse_path(c.get(2));

            path.push(RustPathElem::AssocItem(c[4].to_string()));

            let param = self.lookup_ty_param(&path);

            let Some(param) = param else {
                return "ERR".to_owned();
            };

            annot_meta.add_type(&param);
            format!("{}(RT_xt {})", &c[1], &param.get_rfn_type())
        });

        let cs = RE_ST_OF.replace_all(&cs, |c: &Captures<'_>| {
            let mut path = parse_path(c.get(2));
            path.push(RustPathElem::AssocItem(c[4].to_string()));

            let param = self.lookup_ty_param(&path);

            let Some(param) = param else {
                return "ERR".to_owned();
            };

            annot_meta.add_type(&param);
            format!("{}(ty_syn_type {} MetaNone)", &c[1], param)
        });

        let cs = RE_LY_OF.replace_all(&cs, |c: &Captures<'_>| {
            let mut path = parse_path(c.get(2));
            path.push(RustPathElem::AssocItem(c[4].to_string()));
            let param = self.lookup_ty_param(&path);

            let Some(param) = param else {
                return "ERR".to_owned();
            };

            annot_meta.add_type(&param);
            format!("{}(use_layout_alg' (ty_syn_type {} MetaNone))", &c[1], param)
        });

        let cs = RE_TY_OF.replace_all(&cs, |c: &Captures<'_>| {
            let mut path = parse_path(c.get(2));
            path.push(RustPathElem::AssocItem(c[4].to_string()));
            let param = self.lookup_ty_param(&path);

            let Some(param) = param else {
                return "ERR".to_owned();
            };

            annot_meta.add_type(&param);
            format!("{}{}", &c[1], param)
        });

        let cs = RE_LFT_OF.replace_all(&cs, |c: &Captures<'_>| {
            let t = &c[2];
            let lft = self.lookup_lft(t);

            let Some(lft) = lft else {
                return "ERR".to_owned();
            };

            annot_meta.add_lft(lft.to_owned().into());
            format!("{}{}", &c[1], lft)
        });

        let cs = RE_LIT.replace_all(&cs, |c: &Captures<'_>| {
            let mut path = parse_path(c.get(2));
            path.push(RustPathElem::AssocItem(c[4].to_string()));

            trace!("looking up literal {path:?}");

            // first lookup literals
            let lit = self.lookup_literal(&path);

            if let Some(lit) = lit {
                return format!("{}{}", &c[1], lit);
            }

            // else interpret it as ty_of
            let ty = self.lookup_ty_param(&path);

            if let Some(ty) = ty {
                annot_meta.add_type(&ty);
                return format!("{}{}", &c[1], ty);
            }

            // let's try to parse this as a place
            let content = c[4].to_string();
            if path.len() == 1
                && let Ok((_rest, (place, modifier))) = place_parser::parse_rust_place(&content)
                && let Some(res) = self.lookup_place(&place, modifier)
            {
                return format!("{}{}", &c[1], res);
            }

            "ERR".to_owned()
        });

        let cs = RE_PLACE.replace_all(&cs, |c: &Captures<'_>| {
            // let's try to parse this as a place
            let content = c[2].to_string();
            if let Ok((_rest, (place, modifier))) = place_parser::parse_rust_place(&content)
                && let Some(res) = self.lookup_place(&place, modifier)
            {
                return format!("{}{res}", &c[1]);
            }

            "ERR".to_owned()
        });

        let cs = cs.replace("{{", "{");
        let cs = cs.replace("}}", "}");

        (cs, annot_meta)
    }
}

mod place_parser {
    use nom::branch::alt;
    use nom::bytes::complete::take_while1;
    use nom::character::complete::{char, multispace0};
    use nom::combinator::{map, opt};
    use nom::multi::many0;
    use nom::sequence::{delimited, preceded};
    use nom::{IResult, Parser as _};

    use super::{Projection, Projections, RustPlace};

    fn identifier(input: &str) -> IResult<&str, String> {
        map(take_while1(|c: char| c.is_alphanumeric() || c == '_'), |s: &str| s.to_owned()).parse(input)
    }

    pub(crate) fn parse_rust_place(input: &str) -> IResult<&str, (RustPlace, Option<String>)> {
        let (input, mut place) = proj_place(input)?;

        // Now parse any trailing `.field` chains, no matter what came before
        let (input, fields) = many0(preceded(char('.'), identifier)).parse(input)?;
        place.proj.0.extend(fields.into_iter().map(Projection::Field));

        let (input, modifier) = opt(preceded(char('.'), preceded(char('*'), identifier))).parse(input)?;

        Ok((input, (place, modifier)))
    }

    // proj_place = simple_with_fields | *proj_place | (proj_place)
    fn proj_place(input: &str) -> IResult<&str, RustPlace> {
        alt((deref_place, paren_place, simple_with_fields)).parse(input)
    }

    fn deref_place(input: &str) -> IResult<&str, RustPlace> {
        let (input, _) = preceded(multispace0, char('*')).parse(input)?;
        let (input, mut inner) = proj_place(input)?;
        inner.proj.0.push(Projection::Deref);
        Ok((input, inner))
    }

    fn simple_with_fields(input: &str) -> IResult<&str, RustPlace> {
        let (input, base) = identifier(input)?;
        let (input, fields) = many0(preceded(char('.'), identifier)).parse(input)?;
        let proj = fields.into_iter().map(Projection::Field).collect();
        Ok((input, RustPlace {
            base,
            proj: Projections(proj),
        }))
    }

    fn paren_place(input: &str) -> IResult<&str, RustPlace> {
        delimited(preceded(multispace0, char('(')), proj_place, preceded(multispace0, char(')'))).parse(input)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};

    use super::{ParamLookup, Projection, Projections, RustPath, RustPathElem, RustPlace, specs};

    #[derive(Default)]
    struct TestScope {
        /// conversely, map the declaration name of a lifetime to an index
        lft_names: HashMap<String, specs::LftParam>,

        /// map types to their index
        ty_names: HashMap<String, specs::LiteralTyParam>,

        assoc_names: HashMap<RustPath, specs::LiteralTyParam>,

        literals: HashMap<RustPath, String>,

        places: BTreeMap<RustPlace, String>,
    }

    impl<'def> ParamLookup<'def> for TestScope {
        fn lookup_ty_param(&self, path: &RustPath) -> Option<specs::Type<'def>> {
            if path.len() == 1 {
                let RustPathElem::AssocItem(it) = &path[0];
                if let Some(n) = self.ty_names.get(it) {
                    return Some(specs::Type::LiteralParam(n.to_owned()));
                }
            }

            if let Some(n) = self.assoc_names.get(path) {
                return Some(specs::Type::LiteralParam(n.to_owned()));
            }
            None
        }

        fn lookup_lft(&self, lft: &str) -> Option<&specs::LftParam> {
            self.lft_names.get(lft)
        }

        fn lookup_literal(&self, path: &RustPath) -> Option<String> {
            self.literals.get(path).cloned()
        }

        fn lookup_place(&self, place: &RustPlace, _modifier: Option<String>) -> Option<String> {
            //println!("looking up place {place:?} with modifier {modifier:?}");
            self.places.get(place).cloned()
        }
    }

    #[test]
    fn literal1() {
        let lit = "{rt_of T} * {rt_of T}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("T".to_owned(), specs::LiteralTyParam::new("T"));

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "(T_rt) * (T_rt)");
    }

    #[test]
    fn literal2() {
        let lit = "{ty_of T} * {ty_of T}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("T".to_owned(), specs::LiteralTyParam::new("T"));

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "T_ty * T_ty");
    }

    #[test]
    fn literal3() {
        let lit = "{rt_of Self} * {rt_of Self}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("Self".to_owned(), specs::LiteralTyParam::new("Self"));

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "(Self_rt) * (Self_rt)");
    }

    #[test]
    fn literal4() {
        let lit = "{{rt_of Bla}}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("Self".to_owned(), specs::LiteralTyParam::new("Self"));

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "{rt_of Bla}");
    }

    #[test]
    fn assoc_1() {
        let lit = "{rt_of Bla::Blub}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("Bla".to_owned(), specs::LiteralTyParam::new("Bla"));
        scope.assoc_names.insert(
            vec![RustPathElem::AssocItem("Bla".to_owned()), RustPathElem::AssocItem("Blub".to_owned())],
            specs::LiteralTyParam::new("Bla_Blub"),
        );

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "(Bla_Blub_rt)");
    }

    #[test]
    fn assoc_2() {
        let lit = "{rt_of Bla::Bla::Blub}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("Bla".to_owned(), specs::LiteralTyParam::new("Bla"));
        scope.assoc_names.insert(
            vec![
                RustPathElem::AssocItem("Bla".to_owned()),
                RustPathElem::AssocItem("Bla".to_owned()),
                RustPathElem::AssocItem("Blub".to_owned()),
            ],
            specs::LiteralTyParam::new("Bla_Blub"),
        );

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "(Bla_Blub_rt)");
    }

    #[test]
    fn lit_1() {
        let lit = "{Size} 4";
        let mut scope = TestScope::default();
        scope
            .literals
            .insert(vec![RustPathElem::AssocItem("Size".to_owned())], "(trait_attrs).(size)".to_owned());

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "(trait_attrs).(size) 4");
    }

    #[test]
    fn lit_2() {
        let lit = "{Size_bla} 4";
        let mut scope = TestScope::default();
        scope
            .literals
            .insert(vec![RustPathElem::AssocItem("Size_bla".to_owned())], "(trait_attrs).(size)".to_owned());

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "(trait_attrs).(size) 4");
    }

    #[test]
    fn place_0() {
        let lit = "{a}";
        let mut scope = TestScope::default();
        let exp = RustPlace {
            base: "a".to_owned(),
            proj: Projections(vec![]),
        };
        scope.places.insert(exp, "bla".to_owned());

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "bla");
    }

    #[test]
    fn place_1() {
        let lit = "{a.b}";
        let mut scope = TestScope::default();
        let exp = RustPlace {
            base: "a".to_owned(),
            proj: Projections(vec![Projection::Field("b".to_owned())]),
        };
        scope.places.insert(exp, "bla".to_owned());

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "bla");
    }

    #[test]
    fn place_2() {
        let lit = "{(*a).b.c}";
        let mut scope = TestScope::default();
        let exp = RustPlace {
            base: "a".to_owned(),
            proj: Projections(vec![
                Projection::Deref,
                Projection::Field("b".to_owned()),
                Projection::Field("c".to_owned()),
            ]),
        };
        scope.places.insert(exp, "bla".to_owned());

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "bla");
    }

    #[test]
    fn place_3() {
        let lit = "{*a.b.c}";
        let mut scope = TestScope::default();
        let exp = RustPlace {
            base: "a".to_owned(),
            proj: Projections(vec![
                Projection::Field("b".to_owned()),
                Projection::Field("c".to_owned()),
                Projection::Deref,
            ]),
        };
        scope.places.insert(exp, "bla".to_owned());

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "bla");
    }

    #[test]
    fn place_4() {
        let lit = "{*a.b.c.*new}";
        let mut scope = TestScope::default();
        let exp = RustPlace {
            base: "a".to_owned(),
            proj: Projections(vec![
                Projection::Field("b".to_owned()),
                Projection::Field("c".to_owned()),
                Projection::Deref,
            ]),
        };
        scope.places.insert(exp, "bla".to_owned());

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "bla");
    }

    #[test]
    fn place_5() {
        let lit = "blub ({*a.b.c.*new})";
        let mut scope = TestScope::default();
        let exp = RustPlace {
            base: "a".to_owned(),
            proj: Projections(vec![
                Projection::Field("b".to_owned()),
                Projection::Field("c".to_owned()),
                Projection::Deref,
            ]),
        };
        scope.places.insert(exp, "bla".to_owned());

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "blub (bla)");
    }
}
