use crate::traits::iterator::Iterator;

#[rr::export_as(core::iter::adapters::Skip)]
#[rr::refined_by("(it, n)" : "(_ * nat)")]
pub struct Skip<I> {
    #[rr::field("it")]
    iter: I,
    #[rr::field("Z.of_nat n")]
    n: usize,
}

#[rr::export_as(core::iter::adapters::Skip)]
impl<I> Skip<I> {
    #[rr::returns("(iter, Z.to_nat n)")]
    pub fn new(iter: I, n: usize) -> Skip<I> {
        Skip { iter, n }
    }
}

#[rr::instantiate("Params" := "{MI::Params}")]
#[rr::instantiate("Inv" := "λ π p s, {MI::Inv} π p s.1")]
#[rr::instantiate("Next" := "(λ π p_inner s1 e s2, 
        if_iNone e (
             ∃ seq s2_inner, 
                ⌜length seq ≤ s1.2⌝ ∗ ⌜s2.2 = 0%nat⌝∗ 
                IteratorNextFusedTrans traits_iterator_Iterator_MI_spec_attrs π p_inner s1.1 seq s2_inner ∗
                {MI::Next} π p_inner s2_inner None s2.1) ∗ 
        if_iSome e (λ e, 
            ∃ seq s2_inner, 
                ⌜length seq = s1.2⌝ ∗ ⌜s2.2 = 0%nat⌝∗ 
                IteratorNextFusedTrans traits_iterator_Iterator_MI_spec_attrs π p_inner s1.1 seq s2_inner ∗
                {MI::Next} π p_inner s2_inner (Some e) s2.1))%I")]
impl<MI> Iterator for Skip<MI>
where
    MI: Iterator,
{
    type Item = <MI as Iterator>::Item;

    fn next(&mut self) -> Option<MI::Item> {
        if self.n > 0 {
            let n = self.n;
            self.n = 0;
            self.iter.nth(n)
        } else {
            self.iter.next()
        }
    }
}
