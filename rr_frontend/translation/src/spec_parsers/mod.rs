pub(crate) mod const_attr_parser;
pub(crate) mod crate_attr_parser;
pub(crate) mod enum_spec_parser;
pub(crate) mod loop_attr_parser;
pub(crate) mod module_attr_parser;
pub(crate) mod parse_utils;
pub(crate) mod struct_spec_parser;
pub(crate) mod trait_attr_parser;
pub(crate) mod trait_impl_attr_parser;
pub(crate) mod verbose_function_spec_parser;

use attribute_parse::{MToken, parse};
use parse::{Parse, Peek as _};
use rr_rustc_interface::hir;

/// For parsing of `RustPaths`
#[derive(Debug)]
pub(crate) struct RustPath {
    pub path: Vec<String>,
}

impl<F> Parse<F> for RustPath {
    fn parse(stream: parse::Stream<'_>, meta: &F) -> parse::Result<Self> {
        let x: parse::Punctuated<parse::Ident, MToken![::]> =
            parse::Punctuated::parse_separated_nonempty(stream, meta)?;
        let path = x.into_iter().map(parse::Ident::value).collect();
        Ok(Self { path })
    }
}

/// For parsing of `rr::export_as` annotations
#[derive(Debug)]
pub(crate) struct ExportAs {
    pub path: RustPath,
    /// this is a method
    pub as_method: bool,
}
impl<F> Parse<F> for ExportAs {
    fn parse(stream: parse::Stream<'_>, meta: &F) -> parse::Result<Self> {
        let mut as_method = false;
        if parse::Pound::peek(stream) {
            stream.parse::<_, MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = stream.parse(meta)?;
            match macro_cmd.value().as_str() {
                "method" => {
                    as_method = true;
                },
                _ => {
                    return Err(parse::Error::OtherErr(
                        stream.pos().unwrap(),
                        format!("invalid macro command: {:?}", macro_cmd.value()),
                    ));
                },
            }
        }

        let path: RustPath = stream.parse(meta)?;

        let export = Self { path, as_method };
        Ok(export)
    }
}

pub(crate) fn get_export_as_attr(attrs: &[&hir::AttrItem]) -> Result<ExportAs, String> {
    for &it in attrs {
        let path_segs = &it.path.segments;

        if let Some(seg) = path_segs.get(1) {
            let buffer = parse::Buffer::new(&parse_utils::attr_args_tokens(&it.args));

            if seg.as_str() == "export_as" {
                let path = ExportAs::parse(&buffer, &()).map_err(parse_utils::str_err)?;
                return Ok(path);
            }
        }
    }
    Err("Did not find export_as annotation".to_owned())
}

/// For parsing of `rr::depends_on` annotations
#[derive(Debug)]
pub(crate) struct DependsOn {
    pub paths: Vec<RustPath>,
}
impl<F> Parse<F> for DependsOn {
    fn parse(stream: parse::Stream<'_>, meta: &F) -> parse::Result<Self> {
        let paths: parse::Punctuated<RustPath, MToken![,]> =
            parse::Punctuated::parse_separated_nonempty(stream, meta)?;

        let paths = paths.into_iter().collect();

        let export = Self { paths };
        Ok(export)
    }
}

pub(crate) fn get_depends_on_attrs(attrs: &[&hir::AttrItem]) -> Result<Vec<RustPath>, String> {
    let mut deps = Vec::new();
    for &it in attrs {
        let path_segs = &it.path.segments;

        if let Some(seg) = path_segs.get(1) {
            let buffer = parse::Buffer::new(&parse_utils::attr_args_tokens(&it.args));

            if seg.as_str() == "depends_on" {
                let mut path = DependsOn::parse(&buffer, &()).map_err(parse_utils::str_err)?;
                deps.append(&mut path.paths);
            }
        }
    }
    Ok(deps)
}

/// Parser for getting shim attributes
#[derive(Debug)]
pub(crate) struct ShimAnnot {
    pub code_name: String,
    pub spec_name: String,
    pub trait_req_incl_name: String,
}

impl<U> Parse<U> for ShimAnnot
where
    U: ?Sized,
{
    fn parse(stream: parse::Stream<'_>, meta: &U) -> parse::Result<Self> {
        let pos = stream.pos().unwrap();
        let args: parse::Punctuated<parse::LitStr, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(stream, meta)?;

        if args.len() != 3 {
            return Err(parse::Error::OtherErr(
                pos,
                "Expected exactly three arguments to rr::shim".to_owned(),
            ));
        }

        let args: Vec<_> = args.into_iter().collect();

        Ok(Self {
            code_name: args[0].value(),
            spec_name: args[1].value(),
            trait_req_incl_name: args[2].value(),
        })
    }
}

/// Extract a shim annotation from a list of annotations of a function or method.
pub(crate) fn get_shim_attrs(attrs: &[&hir::AttrItem]) -> Result<ShimAnnot, String> {
    for &it in attrs {
        let path_segs = &it.path.segments;

        if let Some(seg) = path_segs.get(1) {
            let buffer = parse::Buffer::new(&parse_utils::attr_args_tokens(&it.args));

            if seg.as_str() == "shim" {
                let annot = ShimAnnot::parse(&buffer, &()).map_err(parse_utils::str_err)?;
                return Ok(annot);
            }
        }
    }
    Err("Did not find shim annotation".to_owned())
}

/// Parser for getting code shim attributes
#[derive(Debug)]
pub(crate) struct CodeShimAnnot {
    pub code_name: String,
}

impl<U> Parse<U> for CodeShimAnnot
where
    U: ?Sized,
{
    fn parse(stream: parse::Stream<'_>, meta: &U) -> parse::Result<Self> {
        let pos = stream.pos().unwrap();
        let args: parse::Punctuated<parse::LitStr, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(stream, meta)?;

        if args.len() != 1 {
            return Err(parse::Error::OtherErr(
                pos,
                "Expected exactly one argument to rr::code_shim".to_owned(),
            ));
        }
        let args: Vec<_> = args.into_iter().collect();

        Ok(Self {
            code_name: args[0].value(),
        })
    }
}

/// Extract a code shim annotation from a list of annotations of a function or method.
pub(crate) fn get_code_shim_attrs(attrs: &[&hir::AttrItem]) -> Result<CodeShimAnnot, String> {
    for &it in attrs {
        let path_segs = &it.path.segments;

        if let Some(seg) = path_segs.get(1) {
            let buffer = parse::Buffer::new(&parse_utils::attr_args_tokens(&it.args));

            if seg.as_str() == "code_shim" {
                let annot = CodeShimAnnot::parse(&buffer, &()).map_err(parse_utils::str_err)?;
                return Ok(annot);
            }
        }
    }
    Err("Did not find shim annotation".to_owned())
}

/// Check whether we should propagate this attribute of a method from a surrounding impl.
pub(crate) fn propagate_method_attr_from_impl(it: &hir::AttrItem) -> bool {
    if let Some(ident) = it.path.segments.get(1) {
        matches!(ident.as_str(), "context") || matches!(ident.as_str(), "verify")
    } else {
        false
    }
}
