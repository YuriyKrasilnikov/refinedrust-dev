#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![allow(unused)]

#![rr::package("tests")]
#![rr::include("stdlib")]

mod enums;
mod structs;
mod char;
mod traits;
mod trait_deps;
mod trait_derive;
mod statics;
mod vec_client;
mod mixed;
mod closures;
mod references;
mod option;
mod consts;
mod generics;
mod rectypes;
mod loops;

mod lft_constr;

mod latebounds;

//mod leftpad;
