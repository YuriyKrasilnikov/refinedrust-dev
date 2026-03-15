
#[rr::refined_by("()" : "unit")]
#[rr::exists("d" : "{rt_of T}")]
#[rr::exists("c" : "list unit")]
struct Tree<T: Eq> {
    #[rr::field("d")]
    data: T,
    #[rr::field("<#> c")]
    children: Vec<Tree<T>>,
}

impl<T: Eq> Tree<T> {
    #[rr::exists("y")]
    #[rr::returns("y")]
    fn new(d: T) -> Self {
        Tree {
            data: d,
            children: Vec::new(),
        }
    }
}
