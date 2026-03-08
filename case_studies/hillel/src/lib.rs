#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![allow(unused)]

#![rr::package("hillel")]
#![rr::include("stdlib")]


// A port of the Hillel case study from Creusot: https://github.com/creusot-rs/creusot/blob/6c46bc958029c2185e136ed7de15610ff69d027e/tests/should_succeed/hillel.rs


mod wrappers {
    use std::vec::Vec;

    #[rr::only_spec]
    #[rr::requires("index < length x")]
    #[rr::returns("x !!! Z.to_nat index")]
    pub fn vec_index<T>(x: &Vec<T>, index: usize) -> &T {
        &x[index]
    }

    #[rr::only_spec]
    #[rr::returns("x")]
    pub fn vec_iter<T>(x: &Vec<T>) -> core::slice::Iter<'_, T> {
        x.iter()
    }
}
use wrappers::*;


// TODO: feasible to automatically infer bounds sideconditions?
// e.g. with editor integration?

// !start spec(right_pad)
#[rr::requires("size_of_array_in_bytes {st_of T} (2 * Z.to_nat len)%nat ≤ MaxInt isize")]
#[rr::observe("str.ghost": "<#> <$#@{{ {rt_of T} }}> (str.cur ++ replicate (Z.to_nat len - length str.cur) pad)")]
// !end spec
// !start code(right_pad)
fn right_pad<T: Copy>(str: &mut Vec<T>, len: usize, pad: T) {
    while str.len() < len {
        // !end code
        // !start spec(right_pad)
        #[rr::inv_vars("str")]
        #[rr::params("γ", "old_str")]
        #[rr::exists("num" : "nat")]
        #[rr::inv("str = (old_str ++ replicate num pad, γ)")]
        #[rr::inv("(num ≤ Z.to_nat len - length old_str)%nat")]
        #[rr::ignore]||{};
        // !end spec
        // !start code(right_pad)
        str.push(pad);
    }
}
// !end code

// !start spec(left_pad)
#[rr::requires("size_of_array_in_bytes {st_of T} (2 * Z.to_nat len)%nat ≤ MaxInt isize")]
#[rr::observe("str.ghost": "<#> <$#@{{ {rt_of T} }}> (replicate (Z.to_nat len - length str.cur) pad ++ str.cur)")]
// !end spec
// !start code(left_pad)
fn left_pad<T: Copy>(str: &mut Vec<T>, len: usize, pad: T) {
    while str.len() < len {
        // !end code
        // !start spec(left_pad)
        #[rr::inv_vars("str")]
        #[rr::params("γ", "old_str")]
        #[rr::exists("num" : "nat")]
        #[rr::inv("str = (replicate num pad ++ old_str, γ)")]
        #[rr::inv("(num ≤ Z.to_nat len - length old_str)%nat")]
        #[rr::ignore]||{};
        // !end spec
        // !start code(left_pad)
        str.insert(0, pad);
    }
}
// !end code

// !start spec(unique)
#[rr::requires("NoDup vec.cur")]
#[rr::requires("length vec.cur < MaxInt usize")]
#[rr::requires("size_of_array_in_bytes {st_of T} (2 * length vec.cur)%nat ≤ MaxInt isize")]
#[rr::exists("new")] #[rr::observe("vec.ghost" : "$# new")]
#[rr::ensures("NoDup new")]
#[rr::ensures("elem ∈ new")]
#[rr::ensures("vec.cur ⊆ new")]
#[rr::ensures("new ⊆ elem :: vec.cur")]
// !end spec
// !start code(unique)
fn insert_unique<T: Eq>(vec: &mut Vec<T>, elem: T) {
    for e in vec_iter(vec) {
        // !end code
        // !start spec(unique)
        #[rr::inv("elem ∉ {Hist}")]
        #[rr::ignore] ||{};
        // !end spec
        // !start code(unique)
        if e == &elem {
            return;
        }
    }

    vec.push(elem);
}
// !end code

// !start spec(unique)
#[rr::requires("length str < MaxInt usize")]
#[rr::requires("size_of_array_in_bytes {st_of T} (2 * length str)%nat ≤ MaxInt isize")]
#[rr::ensures("NoDup ret")]
#[rr::ensures("str ⊆ ret")]
#[rr::ensures("ret ⊆ str")]
// !end spec
// !start code(unique)
fn unique<T: Eq + Copy>(str: &Vec<T>) -> Vec<T> {
    let mut unique = Vec::new();

    for elem in vec_iter(str) {
        // !end code
        // !start spec(unique)
        #[rr::inv_vars("unique")]
        #[rr::inv("NoDup unique")]
        #[rr::inv("{Hist} ⊆ unique")]
        #[rr::inv("unique ⊆ {Hist}")]
        #[rr::ignore] ||{};
        // !end spec
        // !start code(unique)

        insert_unique(&mut unique, *elem);
    }

    unique
}
// !end code

// !start spec(fulcrum)
// Fulcrum. Given a sequence of integers, returns the index i that minimizes
// |sum(seq[..i]) - sum(seq[i..])|. Does this in O(n) time and O(n) memory.
// Hard
#[rr::requires("s ≠ []")]
#[rr::requires("Hbounded": "∀ x, sublist x s → 0 ≤ sum_list_Z x ≤ MaxInt u32")]
#[rr::ensures("0 ≤ ret < length s")]
#[rr::ensures("∀ i: nat, 0 ≤ i < length s → Z.abs (sum_list_Z (take (Z.to_nat ret) s) - sum_list_Z (drop (Z.to_nat ret) s)) ≤ Z.abs (sum_list_Z (take i s) - sum_list_Z (drop i s))")]
// !end spec
// !start code(fulcrum)
fn fulcrum(s: &Vec<u32>) -> usize {
    let mut total: u32 = 0;

    for &x in vec_iter(s) {
        // !end code
        // !start spec(fulcrum)
        #[rr::inv_vars("total")]
        #[rr::inv("total = sum_list_Z {Hist}")]
        #[rr::ignore] ||{};
        // !end spec
        // !start code(fulcrum)
        total += x;
    }

    let mut min_i: usize = 0;
    let mut min_dist: u32 = total;

    let mut sum: u32 = 0;
    for i in 0..s.len() {
        // !end code
        // !start spec(fulcrum)
        #[rr::inv_vars("sum", "min_i", "min_dist")]
        #[rr::inv("sum = sum_list_Z (take (length {Hist}) s)")]
        #[rr::inv("0 ≤ min_i ≤ length {Hist} ∧ min_i < length s")]
        #[rr::inv("min_dist = Z.abs (sum_list_Z (take (Z.to_nat min_i) s) - sum_list_Z (drop (Z.to_nat min_i) s))")]
        #[rr::inv("Hsmallest": "∀ i: nat, 0 ≤ i < length {Hist} → min_dist ≤ Z.abs (sum_list_Z (take i s) - sum_list_Z (drop i s))")]
        #[rr::ignore] ||{};
        // !end spec
        // !start code(fulcrum)

        let dist = sum.abs_diff(total - sum);
        if dist < min_dist {
            min_i = i;
            min_dist = dist;
        }

        sum += vec_index(s, i);
    }

    min_i
}
// !end code
