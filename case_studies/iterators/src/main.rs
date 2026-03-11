#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![rr::include("stdlib")]

use std::vec::Vec;

mod wrappers {
    use std::vec::Vec;

    #[rr::only_spec]
    #[rr::returns("x")]
    pub fn vec_iter<T>(x: &Vec<T>) -> core::slice::Iter<'_, T> {
        x.iter()
    }
}

use wrappers::*;

fn main() {
    let v = vec![0; 4];
    assert!(counter(v).len() == 2);
}

#[rr::requires("Z.of_nat (length v) ∈ USize")]
#[rr::ensures("length v = length ret")]
pub fn counter(v: Vec<u32>) -> Vec<u32> {
    let mut cnt: usize = 0;

    let x: Vec<u32> = vec_iter(&v)
        .map(
            #[rr::requires("{cnt} + 1 ∈ USize")]
            #[rr::returns("x")]
            #[rr::ensures("{cnt.*new} = {cnt} + 1")]
            |x| {
                cnt += 1;
                *x
            },
        )
        .collect();
    x
}
