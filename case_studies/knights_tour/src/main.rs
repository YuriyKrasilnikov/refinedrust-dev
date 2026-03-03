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

#![rr::include("stdlib")]

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

// #[derive(Copy, Clone)]
#[rr::refined_by("(x, y)" : "Z * Z")]
/* TODO(lennard): copy doesn't work. can't find typeclass instance of Copyable. */
struct Point {
    #[rr::field("x")]
    pub x: isize,
    #[rr::field("y")]
    pub y: isize,
}

impl Point {
    #[rr::requires("int_elem_of_it (self.1 + p.:0) isize")]
    #[rr::requires("int_elem_of_it (self.2 + p.:1) isize")]
    #[rr::returns("(self.1 + p.:0, self.2 + p.:1)")]
    fn mov(&self, p: &(isize, isize)) -> Self {
        Self { x: (self.x + p.0), y: (self.y + p.1) }
    }
}

#[rr::refined_by("(s, f)" : "nat * (list (list nat))")]
#[rr::invariant("s = length f")]
#[rr::invariant("∀ i : nat, i < length f -> length (f !!! i) = s")]
#[rr::exists("field" : "list _")]
#[rr::invariant("field = fmap (λ (x : list nat), #(fmap (λ (y: nat), #(Z.of_nat y)) x) : place_rfn (list (place_rfn Z))) f")]
pub struct Board {
    #[rr::field("Z.of_nat s")]
    pub size: usize,
    #[rr::field("field")]
    pub field: Vec<Vec<usize>>,
}

impl Board {
    // #[logic]
    // fn wf(self) -> bool {
    //     pearlite! {
    //         self.size@ <= 1_000 &&
    //         self.field@.len() == self.size@ &&
    //         forall<i> 0 <= i && i < self.size@ ==> (self.field[i]@).len() == self.size@
    //     }
    // }
    // #[requires(size@ <= 1000)]
    // #[ensures(result.size == size)]
    // #[ensures(result.wf())]
    // #[rr::exists("rows")]
    #[rr::only_spec]
    #[rr::ensures("ret.1 = Z.to_nat size")]
    fn new(size: usize) -> Self {
        let rows = (0..size)
            .map(
                #[rr::requires("True")]
                |_| {
                    vec![0; size]
                    // ::std::vec::from_elem(0, size)
                }
            )
            // .map_inv(
            //     #[ensures(result@.len() == size@)]
            //     |_, _| vec![0; size],
            // )
            .collect();
        Self { size, field: rows }
    }

    // #[requires(self.wf())]
    // #[ensures(result ==> self.in_bounds(p))]
    // #[rr::ensures()]
    #[rr::only_spec]
    #[rr::ensures("ret -> in_bounds self.1 p")]
    /* TODO(lennard): indexing. (not enough simplification) */
    fn available(&self, p: Point) -> bool {
        0 <= p.x
            && (p.x as usize) < self.size
            && 0 <= p.y
            && (p.y as usize) < self.size
            && *vec_index(vec_index(&self.field, p.x as usize), p.y as usize) == 0
    }

    // calculate the number of possible moves
    // #[requires(self.wf())]
    // #[requires(self.in_bounds(p))]
    #[rr::requires("in_bounds self.1 p")]
    #[rr::ensures("ret <= 8")]
    fn count_degree(&self, p: Point) -> usize {
        let mut count = 0;

        for m in moves() {
            #[rr::inv_vars("count")]
            #[rr::invariant("count <= length {Hist}")]
            #[rr::ignore]||{};
            let next = p.mov(&m);
            if self.available(next) {
                count += 1;
            }
        }
        count
    }

    // #[requires(self.wf())]
    // #[requires(self.in_bounds(p))]
    // #[ensures((^self).wf())]
    // #[ensures((^self).size == (*self).size)]
    #[rr::requires("in_bounds self.cur.1 p")]
    #[rr::exists("new_rows" : "list (list nat)")]
    #[rr::observe("self.ghost" : "#(self.cur.1, new_rows)")]
    /* TODO(lennard): indexing. (not enough simplification) */
    fn set(&mut self, p: Point, v: usize) {
        /* use wrapper for indexing: vec_index */
        let idx = vec_index_mut(&mut self.field, p.x as usize);
        *vec_index_mut(idx, p.y as usize) = v;
        // self.field[p.x as usize][p.y as usize] = v
    }
}

// #[trusted]
// #[ensures(result@.len() == 8)]
// #[ensures(forall<i> 0 <= i && i < 8 ==>  -2 <= result[i].0@ && result[i].0@ <= 2 && -2 <= result[i].1@ && result[i].1@ <= 2)]
#[rr::trust_me]
#[rr::returns("[ *[2; 1]; *[1; 2]; *[-1; 2]; *[-2; 1]; *[-2; -1]; *[-1; -2]; *[1; -2]; *[2; -1]]")]
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

// #[ensures(forall<r: &(usize, Point)> result == Some(r) ==>
//           exists<i> 0 <= i && i < v@.len() && v[i] == *r)]
#[rr::ensures("if_Some ret (λ m, m ∈ v)")]
/* TODO(lennard): figure out wth's going wrong */
fn min(v: &Vec<(usize, Point)>) -> Option<&(usize, Point)> {
    let mut min = None;
    // #[invariant(forall<r: &(usize, Point)> min == Some(r) ==>
    //                   exists<i> 0 <= i && i < v@.len() && v[i] == *r)]
    for x in vec_iter(v) {
        #[rr::inv_vars("min")]
        #[rr::invariant("if_Some min (λ m, m ∈ v)")]
        #[rr::ignore]||{};
        match min {
            None => min = Some(x),
            Some(m) => {
                if x.0 < m.0 {
                    min = Some(x)
                }
            }
        };
    }
    min
}

// #[logic]
// #[requires(a@ <= 1_000)]
// #[ensures(a@ * a@ <= 1_000_000)]
// fn dumb_nonlinear_arith(a: usize) {}

// #[requires(0 < size@ && size@ <= 1000)]
// #[requires(x < size)]
// #[requires(y < size)]
// #[rr::requires("x < size")]
// #[rr::requires("y < size")]
// /* TODO(lennard): blocked on point being Copyable */
// pub fn knights_tour(size: usize, x: usize, y: usize) -> Option<Board> {
//     let mut board = Board::new(size);
//     let mut p = Point { x: x as isize, y: y as isize };
//     board.set(p, 1);

//     // snapshot! { dumb_nonlinear_arith(size) };
//     // #[invariant(board.size == size)]
//     // #[invariant(board.wf())]
//     // #[invariant(board.in_bounds(p))]
//     for step in 2..(size * size) {
//         // choose next square by Warnsdorf's rule
//         #[rr::inv_vars("size", "board", "p")]
//         #[rr::invariant("board.1 = size")]
//         #[rr::invariant("in_bounds board.1 p")]
//         #[rr::ignore]||{};
//         let mut candidates: Vec<(usize, Point)> = Vec::new();
//         // #[invariant(forall<i> 0 <= i && i < candidates@.len() ==>
//         //             board.in_bounds(candidates[i].1))]
//         for m in moves() {
//             #[rr::inv_vars("candidates", "board")]
//             #[rr::invariant("∀ x, x ∈ candidates -> in_bounds board.1 x.:1")]
//             #[rr::ignore]||{};
//             // proof_assert! { forall<r:Seq<_>, a: Seq<_>, b:Seq<_>> r == a.concat(Seq::singleton(m).concat(b)) ==> m == r[a.len()] };
//             let adj = p.mov(&m);
//             if board.available(adj) {
//                 let degree = board.count_degree(adj);
//                 candidates.push((degree, adj));
//             }
//         }
//         match min(&candidates) {
//             Some(&(_, adj)) => p = adj,
//             None => return None,
//         };
//         board.set(p, step);
//     }
//     Some(board)
// }

const SIZE : i64 = 5;

fn main() {
    let (x, y) = (3, 1);
    println!("Board size: {}", SIZE);
    println!("Starting position: ({}, {})", x, y);
    // match knights_tour(x, y) {
    //     Some(b) => print!("{}", b),
    //     None => println!("Fail!"),
    // }
}
