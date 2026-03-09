#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![allow(unused)]

#![feature(try_trait_v2)]
#![feature(unboxed_closures)]
#![feature(try_blocks)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.iterator")]
#![rr::include("closures")]
#![rr::include("option")]
#![rr::include("result")]
#![rr::include("controlflow")]


mod step;
pub mod adapters;
pub mod traits;

