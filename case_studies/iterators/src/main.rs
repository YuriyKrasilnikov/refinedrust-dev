#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![rr::package("iterators")]
#![feature(allocator_api)]
#![rr::include("stdlib")]

use std::vec::Vec;
use std::alloc::Allocator;

mod wrappers {
    use std::vec::Vec;

    #[rr::only_spec]
    #[rr::returns("x")]
    pub fn vec_iter<T>(x: &Vec<T>) -> core::slice::Iter<'_, T> {
        x.iter()
    }

    #[rr::only_spec]
    #[rr::exists("γs")]
    #[rr::ensures("length γs = length x.cur")]
    #[rr::observe("x.ghost": "(PlaceGhost <$> γs) : list (place_rfn {rt_of T})")]
    #[rr::returns("zip x.cur γs")]
    pub fn vec_iter_mut<T>(x: &mut Vec<T>) -> core::slice::IterMut<'_, T> {
        x.iter_mut()
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

#[rr::returns("seqZ 0 10")]
fn test_iterator_1() -> Vec<i32> {
    (0..10).collect()
}

#[rr::returns("seqZ 0 10")]
fn test_iterator_2() -> Vec<i32> {
    (0..10).map(#[rr::returns("x")] |x| x).collect()
}

#[rr::returns("seqZ 0 10")]
fn test_iterator_3() -> Vec<i32> {
    let mut y = 0;
    let res = (0..10).map(
        #[rr::requires("1 + {y} ∈ i32")]
        #[rr::ensures("{y.*new} = 1 + {y}")]
        #[rr::returns("x")] |x| { y += 1; x }).collect();

    assert!(y == 10);

    res
}

#[rr::observe("v.ghost" : "<#> replicate (length v.cur) 0")]
pub fn all_zero(v: &mut Vec<usize>) {
    for x in vec_iter_mut(v) {
        #[rr::invariant(#iris "ObsList ({Hist}.*2) (replicate (length {Hist}) 0)")]
        #[rr::ignore] || {};
        *x = 0;
    }
}

#[rr::returns("(λ x, x * 10) <$> seqZ 0 10")]
pub fn decuple_range() -> Vec<u32> {
    let v: Vec<_> = (0..10)
        .map(
            #[rr::requires("x < 100")]
            #[rr::returns("x * 10")]
            |x: u32| x * 10
        )
        .collect();
    v
}

#[rr::params("p")] 
#[rr::requires(#iris "{I::Inv} π p iter")]
pub fn skip_take<I: Iterator>(iter: I, n: usize) {
    let res = iter.take(n).skip(n).next();

    assert!(res.is_none());
}

#[rr::returns("v1 ++ v2")]
pub fn extend_index(mut v1: Vec<u32>, v2: Vec<u32>) -> Vec<u32> {
    Extend::extend(&mut v1, v2.into_iter());
    v1
}

/// Axiomatized version of extend to get the same spec as Creusot without Vec bounds checking.
#[rr::exists("ExtendResult" : "{xt_of Self} → list {xt_of A} → {xt_of Self}")]
pub trait Extend<A> {
    #[rr::params("p")]
    #[rr::requires(#iris "{T::Inv} π p iter")]
    #[rr::exists("seq", "s2", "s2'")]
    #[rr::ensures(#iris "IteratorNextFusedTrans traits_iterator_Iterator_T_spec_attrs π p iter seq s2")]
    #[rr::ensures(#iris "{T::Next} π p s2 None s2'")]
    #[rr::observe("self.ghost": "$#@{{ {rt_of Self} }} ({ExtendResult} self.cur seq)")]
    fn extend<T: Iterator<Item = A>>(&mut self, iter: T);
}

#[rr::only_spec]
#[rr::instantiate("ExtendResult" := "λ self other, self ++ other")]
impl<T, A: Allocator> Extend<T> for Vec<T, A> {
    fn extend<I: Iterator<Item = T>>(&mut self, iter: I) {
        unimplemented!();
    }
}
