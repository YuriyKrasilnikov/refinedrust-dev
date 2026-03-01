

#[rr::returns("seqZ 0 10")]
fn test_iterator_1() -> Vec<i32> {
    (0..10).collect()
}

#[rr::returns("seqZ 0 10")]
fn test_iterator_2() -> Vec<i32> {
    (0..10).map(#[rr::returns("x")] |x| x).collect()
}
