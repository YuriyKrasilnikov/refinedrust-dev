// extern crate creusot_std;
// use creusot_std::{
//     prelude::{vec, *},
//     std::clone::Clone,
// };
#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![rr::import("refinedrust.examples.knights_tour.theories", "defs")]
#![rr::package("knights-tour")]
#![rr::include("stdlib")]

mod wrappers {
    #[rr::only_spec]
    #[rr::requires("index < length x.cur")]
    #[rr::exists("γi")]
    #[rr::returns("(x.cur !!! Z.to_nat index, γi)")]
    #[rr::observe("x.ghost": "<[Z.to_nat index := PlaceGhost γi]> (<$#> x.cur)")]
    pub fn vec_index_mut<T>(x: &mut Vec<T>, index: usize) -> &mut T {
        &mut x[index]
    }

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

#[derive(Copy, Clone)]
// !start spec(knights_tour.point)
#[rr::refined_by("(x, y)" : "Z * Z")]
// !end spec
struct Point {
    // !start spec(knights_tour.point)
    #[rr::field("x")]
    // !end spec
    pub x: isize,
    // !start spec(knights_tour.point)
    #[rr::field("y")]
    // !end spec
    pub y: isize,
}

impl Point {
    // !start spec(knights_tour.mov)
    #[rr::requires("int_elem_of_it (self.1 + p.:0) isize")]
    #[rr::requires("int_elem_of_it (self.2 + p.:1) isize")]
    #[rr::returns("(self.1 + p.:0, self.2 + p.:1)")]
    // !end spec
    // !start code(knights_tour.mov)
    fn mov(&self, p: &(isize, isize)) -> Self {
        Self {
            x: (self.x + p.0),
            y: (self.y + p.1),
        }
    }
    // !end code

    // !start spec(knights_tour.point)
    #[rr::returns("(x, y)")]
    // !end spec
    // !start code(knights_tour.point)
    fn new(x: isize, y: isize) -> Self {
        Self { x: x, y: y }
    }
    // !end code
}

// !start spec(knights_tour.board)
#[rr::refined_by("(s, f)" : "nat * (list (list Z))")]
#[rr::exists("field" : "list _")]
#[rr::invariant("field = fmap (λ (x : list Z), #(fmap (λ (y: Z), #y) x) : place_rfn (list (place_rfn Z))) f")]
#[rr::invariant("s = length f")]
#[rr::invariant("Hnestedlen" : "∀ i : nat, i < length f → length (f !!! i) = s")]
// !end spec
pub struct Board {
    // !start spec(knights_tour.board)
    #[rr::field("Z.of_nat s")]
    // !end spec
    pub size: usize,
    // !start spec(knights_tour.board)
    #[rr::field("field")]
    // !end spec
    pub field: Vec<Vec<usize>>,
}

impl Board {
    // !start spec(knights_tour.new)
    #[rr::requires("Z.to_nat 16 * size ∈ isize")]
    #[rr::ensures("ret.1 = Z.to_nat size")]
    // !end spec
    // !start code(knights_tour.new)
    fn new(size: usize) -> Self {
        let rows = (0..size)
            .map(
                // !end code
                // !start spec(knights_tour.new)
                #[rr::requires("Z.to_nat 16 * {size} ∈ isize")]
                #[rr::returns("replicate (Z.to_nat {size}) 0")]
                // !end spec
                // !start code(knights_tour.new)
                |_| vec![0; size],
            )
            .collect();
        Self { size, field: rows }
    }
    // !end code

    // !start spec(knights_tour.available)
    #[rr::ensures("if ret then in_bounds self.1 p else True")]
    // !end spec
    // !start code(knights_tour.available)
    fn available(&self, p: Point) -> bool {
        0 <= p.x
            && (p.x as usize) < self.size
            && 0 <= p.y
            && (p.y as usize) < self.size
            && *vec_index(vec_index(&self.field, p.x as usize), p.y as usize) == 0
    }
    // !end code

    // !start spec(knights_tour.count_degree)
    #[rr::requires("in_bounds self.1 p")]
    #[rr::requires("p.1 + 2 ∈ isize ∧ p.1 - 2 ∈ isize ∧ p.2 + 2 ∈ isize ∧ p.2 - 2 ∈ isize")]
    #[rr::requires("size_of_array_in_bytes (tuple2_sls (IntSynType isize) (IntSynType isize)) 16 ≤ MaxInt isize")]
    #[rr::ensures("ret ≤ 8")]
    // !end spec
    // !start code(knights_tour.count_degree)
    fn count_degree(&self, p: Point) -> usize {
        let mut count = 0;

        for m in moves() {
            // !end code
            // !start spec(knights_tour.count_degree)
            #[rr::inv_vars("count")]
            #[rr::invariant("count <= length {Hist}")]
            #[rr::ignore] || {};
            // !end spec
            // !start code(knights_tour.count_degree)
            let next = p.mov(&m);
            if self.available(next) {
                count += 1;
            }
        }
        count
    }
    // !end code

    // !start spec(knights_tour.count_degree)
    #[rr::requires("in_bounds self.cur.1 p")]
    #[rr::exists("new_rows" : "list (list Z)")]
    #[rr::observe("self.ghost" : "(self.cur.1, new_rows)")]
    // !end spec
    // !start code(knights_tour.count_degree)
    fn set(&mut self, p: Point, v: usize) {
        let idx = vec_index_mut(&mut self.field, p.x as usize);
        *vec_index_mut(idx, p.y as usize) = v;
    }
    // !end code
}

// !start spec(knights_tour.count_degree)
#[rr::requires("Hbounds": "size_of_array_in_bytes (tuple2_sls (IntSynType isize) (IntSynType isize)) 16 ≤ MaxInt isize")]
#[rr::ensures("∀ (a b : Z), *[a; b] ∈ ret -> (a ≤ 2)%Z ∧ (-2 ≤ a)%Z ∧ (b ≤ 2)%Z ∧ (-2 ≤ b)%Z")]
#[rr::ensures("length ret = 8%nat")]
// !end spec
// !start code(knights_tour.count_degree)
fn moves() -> Vec<(isize, isize)> {
    let mut v = Vec::new();
    v.push((2, 1));
    v.push((1, 2));
    v.push((-1, 2));
    v.push((-2, 1));
    v.push((-2, -1));
    v.push((-1, -2));
    v.push((1, -2));
    v.push((2, -1));
    v
}
// !end code

// !start spec(knights_tour.min)
#[rr::ensures("if_Some ret (λ m, m ∈ v)")]
// !end spec
// !start code(knights_tour.min)
fn min(v: &Vec<(usize, Point)>) -> Option<(usize, Point)> {
    let mut min: Option<(usize, Point)> = None;
    for x in vec_iter(v) {
        // !end code
        // !start spec(knights_tour.min)
        #[rr::inv_vars("min")]
        #[rr::invariant("if_Some min (λ m, m ∈ v)")]
        #[rr::ignore] || {};
        // !end spec
        // !start code(knights_tour.min)
        match &min {
            None => min = Some(*x),
            Some(m) => {
                if x.0 < m.0 {
                    min = Some(*x)
                }
            }
        };
    }
    min
}
// !end code

// !start spec(knights_tour.knights_tour)
#[rr::requires("Hx_upper": "a < size")]
#[rr::requires("Hy_upper": "b < size")]
#[rr::requires("16 * size ∈ isize")]
#[rr::requires("size * size ∈ usize")]
#[rr::requires("size_of_array_in_bytes (tuple2_sls (IntSynType usize) Point_sls) 16 ≤ MaxInt isize")]
#[rr::requires("size_of_array_in_bytes (tuple2_sls (IntSynType isize) (IntSynType isize)) 16 ≤ MaxInt isize")]
// !end spec
// !start code(knights_tour.knights_tour)
pub fn knights_tour(size: usize, a: usize, b: usize) -> Option<Board> {
    let mut board = Board::new(size);
    let mut p = Point::new(a as isize, b as isize);
    board.set(p, 1);

    for step in 2..(size * size) {
        // choose next square by Warnsdorf's rule
        // !end code
        // !start spec(knights_tour.knights_tour)
        #[rr::inv_vars("board", "p")]
        #[rr::invariant("board.1 = Z.to_nat size")]
        #[rr::invariant("Hboard_inbounds": "in_bounds board.1 p")]
        #[rr::ignore]||{};
        // !end spec
        // !start code(knights_tour.knights_tour)
        let mut candidates: Vec<(usize, Point)> = Vec::new();
        for m in moves() {
            // !end code
            // !start spec(knights_tour.knights_tour)
            #[rr::params("init_board")]
            #[rr::inv_vars("candidates", "board")]
            #[rr::invariant("board = init_board")]
            #[rr::invariant("Hcandidate_bounds": 
                "∀ (z : RT_xt (place_rfnRT (tuple2_rt Z Point_inv_t_rt))), z ∈ candidates → in_bounds board.1 (z.:1)"
            )]
            #[rr::invariant("length candidates ≤ length {Hist}")]
            #[rr::ignore]||{};
            // !end spec
            // !start code(knights_tour.knights_tour)
            let adj = p.mov(&m);
            if board.available(adj) {
                let degree = board.count_degree(adj);
                candidates.push((degree, adj));
            }
        }
        match min(&candidates) {
            Some((_, adj)) => p = adj,
            None => return None,
        };
        board.set(p, step);
    }
    Some(board)
}
// !end code

const SIZE: i64 = 5;

fn main() {
    let (x, y) = (3, 1);
    println!("Board size: {}", SIZE);
    println!("Starting position: ({}, {})", x, y);
     //match knights_tour(10000, x, y) {
         //Some(b) => print!("{}", b),
         //None => println!("Fail!"),
     //}
}
