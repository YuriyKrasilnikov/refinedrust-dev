

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
