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

// !start spec(counter)
#[rr::returns("v")]
// !end spec
// !start code(counter)
pub fn counter(v: Vec<u32>) -> Vec<u32> {
    let mut cnt: usize = 0;

    let x: Vec<u32> = vec_iter(&v)
        .map(
            // !end code
            // !start spec(counter)
            #[rr::requires("{cnt} + 1 ∈ USize")]
            #[rr::returns("x")]
            #[rr::ensures("{cnt.*new} = {cnt} + 1")]
            // !end spec
            // !start code(counter)
            |x| {
                cnt += 1;
                *x
            },
        )
        .collect();
    assert!(cnt == x.len());
    x
}
// !end code

#[rr::requires("n >= 0")]
#[rr::returns("n")]
pub fn sum_range(n: isize) -> isize {
    let mut i = 0;
    for _ in 0..n {
        #[rr::inv_vars("i")]
        #[rr::inv("i = length {Hist}")]
        #[rr::ignore]||{};
        i += 1;
    }
    i
}

#[rr::requires("Z.of_nat (length vec) ∈ USize")]
#[rr::returns("length vec")]
pub fn vec_len<T>(vec: &Vec<T>) -> usize {
    let mut i = 0;
    for _ in vec_iter(vec) {
        #[rr::inv_vars("i")]
        #[rr::inv("i = length {Hist}")]
        #[rr::ignore]||{};
        i += 1
    }
    i
}
