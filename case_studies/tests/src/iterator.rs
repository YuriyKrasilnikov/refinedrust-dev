

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


#[rr::only_spec]
#[rr::exists("γs")]
#[rr::ensures("length γs = length x.cur")]
#[rr::observe("x.ghost": "(PlaceGhost <$> γs) : list (place_rfn {rt_of T})")]
#[rr::returns("zip x.cur γs")]
pub fn vec_iter_mut<T>(x: &mut Vec<T>) -> core::slice::IterMut<'_, T> {
    x.iter_mut()
}
