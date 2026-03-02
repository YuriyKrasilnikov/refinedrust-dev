#![rr::import("rrstd.iterator.theories", "map")]

use crate::traits::iterator::Iterator;


// Some alternative ideas:
// - I have an invariant field that iterators must satisfy to call next. 
// - this invariant should be abstract to the user of the iterator, i.e. we shouldn't unfold it.
// - This is basically just a way to move the iterator invariant out of the data structure...
//   but let's try it.



#[rr::export_as(core::iter::adapters::Map)]
#[rr::refined_by("x" : "MapXRT {rt_of I} {rt_of F}")]
pub struct Map<I, F> 
{
    #[rr::field("$# x.(map_it)")]
    pub(crate) iter: I,
    #[rr::field("$# x.(map_clos)")]
    f: F,
}

#[rr::export_as(core::iter::adapters::Map)]
impl<I, F> Map<I, F> 
{
    #[rr::returns("mk_map_x iter f")]
    pub(crate) fn new(iter: I, f: F) -> Map<I, F> {
        Map { iter, f }
    }

    pub(crate) fn into_inner(self) -> I {
        self.iter
    }
}

/// Spec: We have the pure parts of the inner Next and the pre- and postconditions.
#[rr::instantiate("Next" := "(λ π s1 e s2, 
        if_iNone e ({MI::Next} π s1.(map_it) None s2.(map_it)) ∗
        if_iSome e (λ e, ∃ e_inner,
            ({MI::Next} π s1.(map_it) (Some e_inner) s2.(map_it)) ∗
            ∃ p, boringly ({MF::Pre} π p s1.(map_clos) *[e_inner]) ∗
            ({MF::PostMut} π p s1.(map_clos) *[e_inner] s2.(map_clos) e)
            ))%I")]
#[rr::instantiate("Inv" := "MapInv traits_iterator_Iterator_MI_spec_attrs {MF::Pre} {MF::PostMut}")]
impl<MB, MI: Iterator, MF> Iterator for Map<MI, MF>
where
    MF: FnMut(MI::Item) -> MB,
{
    type Item = MB;

    #[rr::default_spec]
    fn next(&mut self) -> Option<MB> {
        self.iter
            .next()
            .map(&mut self.f)
    }
}
