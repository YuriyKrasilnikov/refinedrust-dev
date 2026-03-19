#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::include("stdlib")]

mod basic_ops;
mod lifecycle;
mod patterns;
mod expected_fail;
