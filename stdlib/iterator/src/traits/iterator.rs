
#![rr::import("rrstd.iterator.theories", "iterator")]

use crate::adapters::map::Map;
use std::ops::{ControlFlow, Try};

// example for state changes on None:
// - fusing iterator (make any iterator Fused)

/// Spec: A relation
#[rr::export_as(core::iter::Iterator)]
#[rr::external_attrs("Params", "Inv", "Next")]
//#[rr::exists("Next" : "thread_id → {xt_of Self} → option {xt_of Item} → {xt_of Self} → iProp Σ")]
//#[rr::exists("Inv" : "thread_id → {xt_of Self} → iProp Σ")]
pub trait Iterator {
    type Item;

    #[rr::params("p")]
    #[rr::requires(#iris "{Inv} π p self.cur")]
    /// Postcondition: There exists an optional next item and the successor state of the iterator.
    #[rr::exists("new_it_state" : "{xt_of Self}")]
    /// Postcondition: The state of the iterator has been updated.
    #[rr::observe("self.ghost": "($# new_it_state)")]
    /// Postcondition: If there is a next item, it obeys the iterator's relation, and similarly the
    /// successor state is determined.
    #[rr::ensures(#iris "{Next} π p self.cur ret new_it_state")]
    #[rr::ensures(#iris "{Inv} π p new_it_state")]
    fn next(&mut self) -> Option<Self::Item>;

    /// We pick an invariant Inv
    /// TODO: maybe release Inv when we drop the Map iterator
    #[rr::params("p_inner", "Inv" : "map_inv_ty _ _ _ _ FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs")]
    #[rr::params("ParamPred" : "clos_param_pred_ty _ _ _ FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs")]
    #[rr::requires(#iris "{Inv} π p_inner self")]
    /// Precondition: The picked invariant should hold initially.
    #[rr::requires(#iris "Inv π self f")]
    /// Precondition: persistently, each iteration preserves the invariant.
    /// If the inner iterator has been advanced, we can call the closure.
    #[rr::requires(#iris "□ (∀ it_state it_state' clos_state e,
        (☒ {Self::Next} π p_inner it_state (Some e) it_state') -∗
        Inv π it_state clos_state -∗
        ∃ pclos, ⌜ParamPred *[e] pclos⌝ ∗ {F::Pre} π pclos clos_state *[e] ∗
        (∀ e' clos_state', ☒ {F::PostMut} π pclos clos_state *[e] clos_state' e' -∗ Inv π it_state' clos_state' ∗ True))")]
    /// Precondition: If no element is emitted, the invariant is also upheld.
    #[rr::requires(#iris "□ (∀ it_state it_state' clos_state,
        (☒ {Self::Next} π p_inner it_state None it_state') -∗
        Inv π it_state clos_state -∗
        Inv π it_state' clos_state ∗ True)")]
    #[rr::ensures("ret = mk_map_x self f")]
    // TODO: spec shortcut to refer to attrs of Self
    #[rr::ensures(#iris "traits_iterator_Iterator_Inv (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs _ _ _ _ traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs) π (p_inner, ParamPred) ret")]
    fn map<B, F>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> B,
    {
        Map::new(self, f)
    }

    /*
    /// Specification: we iterate until we fail. 
    /// Postcondition: we get a bigsep of the postconditions of the closure calls that succeeded.
    fn try_for_each<F, R>(&mut self, f: F) -> R
    where
        Self: Sized,
        F: FnMut(Self::Item) -> R,
        R: Try<Output = ()>,
    {
        #[inline]
        fn call<T, R>(mut f: impl FnMut(T) -> R) -> impl FnMut((), T) -> R {
            move |(), x| f(x)
        }

        unimplemented!();
        //self.try_fold((), call(f))
    }
    */

    #[rr::trust_me]
    #[rr::params("p")]
    #[rr::requires(#iris "{Inv} π p self")]
    #[rr::exists("seq", "s2", "s2'")]
    #[rr::ensures(#iris "{Next} π p s2 None s2'")]
    // TODO: have an escape to refer to the attrs record instead
    #[rr::ensures(#iris "IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq s2")]
    // Extract observations from dropping self.
    #[rr::ensures(#iris "ty_ghost_drop {Self} π ($# s2)")]
    #[rr::returns("{B::FromSequence} seq")]
    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        // This is too aggressive to turn on for everything all the time, but PR#137908
        // accidentally noticed that some rustc iterators had malformed `size_hint`s,
        // so this will help catch such things in debug-assertions-std runners,
        // even if users won't actually ever see it.
        //if cfg!(debug_assertions) {
            //let hint = self.size_hint();
            //assert!(hint.1.is_none_or(|high| high >= hint.0), "Malformed size_hint {hint:?}");
        //}

        FromIterator::from_iter(self)
    }


    #[rr::params("p", "P" : "{xt_of Self::Item} → Prop", "ClosInv" : "map_inv_ty  _ _ _ _ FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs")]
    #[rr::requires(#iris "{Inv} π p self.cur")]
    #[rr::requires(#iris "ClosInv π self.cur f")]
    /// Precondition: If the inner iterator has been advanced, we can call the closure.
    #[rr::requires(#iris "□ (∀ it_state it_state' clos_state e,
        {Self::Next} π p it_state (Some e) it_state' -∗
        ClosInv π it_state clos_state -∗
        ∃ pclos, {F::Pre} π pclos clos_state *[e] ∗
        {Self::Next} π p it_state (Some e) it_state' ∗ 
        (∀ b clos_state', {F::PostMut} π pclos clos_state *[e] clos_state' b -∗ ⌜b = true ↔ P e⌝ ∗ ClosInv π it_state' clos_state'))")]
    #[rr::exists("seq", "s2", "s2'")]
    // Postcondition: We consume a sequence of elements from the iterator
    #[rr::ensures(#iris "IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self.cur seq s2")]
    // If true is returned, the whole iterator was consumed; otherwise, the last element didn't pass the check
    #[rr::ensures(#iris "if_iTrue ret ({Next} π p s2 None s2' ∗ ⌜Forall P seq⌝)")]
    #[rr::ensures(#iris "if_iFalse ret (⌜s2 = s2'⌝ ∗ ∃ seq' e, ⌜seq = seq' ++ [e]⌝ ∗ ⌜Forall P seq'⌝ ∗ ⌜¬ P e⌝)")]
    // Postcondition: the invariant is upheld
    #[rr::ensures(#iris "{Inv} π p s2'")]
    // Postcondition: the iterator is updated to the new state
    #[rr::observe("self.ghost": "$# s2'")]
    fn all<F>(&mut self, mut f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        matches!(self.try_fold((), 
            #[rr::params("pclos")]
            #[rr::requires(#iris "{F::Pre} π pclos {f} *[b]")] 
            #[rr::exists("res" : "bool")]
            #[rr::ensures(#iris "{F::PostMut} π pclos {f} *[b] {f.*new} res")]
            #[rr::returns("if res then Ok tt else Err tt")]
            |_, b| { if f(b) { ControlFlow::Continue(()) } else { ControlFlow::Break(()) } }), ControlFlow::Continue(_))
    }

    #[rr::only_spec]
    #[rr::params("p", "P" : "{xt_of Self::Item} → Prop", "ClosInv" : "map_inv_ty  _ _ _ _ FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs")]
    #[rr::requires(#iris "{Inv} π p self.cur")]
    #[rr::requires(#iris "ClosInv π self.cur f")]
    /// Precondition: If the inner iterator has been advanced, we can call the closure.
    #[rr::requires(#iris "□ (∀ it_state it_state' clos_state e,
        {Self::Next} π p it_state (Some e) it_state' -∗
        ClosInv π it_state clos_state -∗
        ∃ pclos, {F::Pre} π pclos clos_state *[e] ∗
        {Self::Next} π p it_state (Some e) it_state' ∗ 
        (∀ b clos_state', {F::PostMut} π pclos clos_state *[e] clos_state' b -∗ ⌜b = true ↔ P e⌝ ∗ ClosInv π it_state' clos_state'))")]
    #[rr::exists("seq", "s2", "s2'")]
    // Postcondition: We consume a sequence of elements from the iterator
    #[rr::ensures(#iris "IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self.cur seq s2")]
    // For all emitted elements, the predicate is not satisfied
    #[rr::ensures("Forall (λ x, ¬ P x) seq")]
    // Postcondition: if None is returned, the whole iterator was consumed
    #[rr::ensures(#iris "if_iNone ret ({Next} π p s2 None s2')")]
    // Postcondition: if we find an index, then the element satisfies the predicate
    #[rr::ensures(#iris "if_iSome ret (λ idx, ⌜length seq = Z.to_nat idx⌝ ∗ ∃ e, {Next} π p s2 (Some e) s2' ∗ ⌜P e⌝)")]
    // Postcondition: the invariant is upheld
    #[rr::ensures(#iris "{Inv} π p s2'")]
    // Postcondition: the iterator is updated to the new state
    #[rr::observe("self.ghost": "$# s2'")]
    fn position<F>(&mut self, f: F) -> Option<usize>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        unimplemented!();
    }

    #[rr::only_spec]
    #[rr::params("p")]
    #[rr::requires(#iris "{Inv} π p self")]
    #[rr::exists("seq", "s2", "s2'")]
    // first: gain knowledge that iterator has ended (better for simplification)
    #[rr::ensures(#iris "{Next} π p s2 None s2'")]
    // TODO: have an escape to refer to the attrs record instead
    #[rr::ensures(#iris "IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq s2")]
    // TODO: fix: reference {Self::Item::Ord}
    #[rr::returns("max_list_cmp Ord_Selfastraits_iterator_Iterator_Item_spec_attrs.(Ord_Ord) seq None")]
    fn max(self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        unimplemented!();
        //self.max_by(Ord::cmp)
    }

    #[rr::only_spec]
    #[rr::params("p")]
    #[rr::requires(#iris "{Inv} π p self")]
    #[rr::exists("seq", "s2", "s2'")]
    #[rr::ensures(#iris "{Next} π p s2 None s2'")]
    // TODO: have an escape to refer to the attrs record instead
    #[rr::ensures(#iris "IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq s2")]
    // TODO: fix: reference {Self::Item::Ord}
    #[rr::returns("min_list_cmp Ord_Selfastraits_iterator_Iterator_Item_spec_attrs.(Ord_Ord) seq None")]
    fn min(self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        unimplemented!();
        //self.max_by(Ord::cmp)
    }

    // Closure inv gets accumulator, iterator state and closure state 
    // P is a predicate over elements of the iterator. TODO: generalize to include the accumulator?
    #[rr::params("p", "P" : "{xt_of Self::Item} → Prop", "ClosInv" : "thread_id → {xt_of B} → {xt_of Self} → {xt_of F} → iProp Σ")]
    #[rr::requires(#iris "{Inv} π p self.cur")]
    #[rr::requires(#iris "ClosInv π init self.cur f")]
    #[rr::requires(#iris "□ (∀ acc it_state it_state' clos_state e,
        {Self::Next} π p it_state (Some e) it_state' -∗
        ClosInv π acc it_state clos_state -∗
        ∃ pclos, {F::Pre} π pclos clos_state *[acc; e] ∗
        {Self::Next} π p it_state (Some e) it_state' ∗ 
        (∀ b clos_state', {F::PostMut} π pclos clos_state *[acc; e] clos_state' b -∗ 
            if_iOk ({R::BranchFn} b) (λ new_acc, ⌜P e⌝ ∗ ClosInv π new_acc it_state' clos_state') ∗ 
            if_iErr ({R::BranchFn} b) (λ err, ⌜¬ P e⌝ ∗ True)
            ))")]
    #[rr::exists("seq", "s2", "s2'")]
    // We observe a sequence of elements emitted from the iterator.
    #[rr::observe("self.ghost": "$# s2'")]
    #[rr::ensures(#iris "{Inv} π p s2'")]
    #[rr::ensures(#iris "IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self.cur seq s2")]
    // If Ok is returned, then we fully consumed the iterator.
    // TODO: currently, we don't state much of anything about the accumulator, just about the
    // sequence of elements.
    #[rr::ensures(#iris "if_iOk ({R::BranchFn} ret) (λ ret, 
            {Next} π p s2 None s2' ∗ 
            ⌜Forall P seq⌝ 
            )")]
    #[rr::ensures(#iris "if_iErr ({R::BranchFn} ret) (λ err, 
               ⌜s2 = s2'⌝∗ 
               ∃ seq' e, ⌜seq = seq' ++ [e]⌝ ∗  
               ⌜Forall P seq'⌝ ∗ ⌜¬ P e⌝
            )")]
    fn try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: Try<Output = B>,
    {
        let mut accum = init;
        while let Some(x) = self.next() {
            #[rr::params("γ", "init_state")]
            #[rr::inv_vars("self", "accum", "f")]
            #[rr::invariant("self.ghost = γ")]
            #[rr::exists("seq")]
            #[rr::invariant(#iris "IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p init_state seq self.cur")]
            #[rr::invariant(#iris "{Inv} π p self.cur")]
            #[rr::invariant(#iris "ClosInv π accum self.cur f")]  
            #[rr::invariant("Forall P seq")]
            #[rr::ignore] || {};
            accum = f(accum, x)?;
        }
        try { accum }
    }

    #[rr::params("p", "P" : "list {xt_of Self::Item} → {xt_of B} → Prop", "ClosInv" : "thread_id → {xt_of B} → {xt_of Self} → {xt_of F} → iProp Σ")]
    #[rr::requires(#iris "{Inv} π p self")]
    #[rr::requires(#iris "ClosInv π init self f")]
    #[rr::requires("P [] init")]
    #[rr::requires(#iris "□ (∀ seq acc it_state it_state' clos_state e,
        IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq it_state -∗ 
        {Self::Next} π p it_state (Some e) it_state' -∗
        ClosInv π acc it_state clos_state -∗
        ∃ pclos, {F::Pre} π pclos clos_state *[acc; e] ∗
        {Self::Next} π p it_state (Some e) it_state' ∗ 
        IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq it_state∗ 
        (∀ acc' clos_state', 
            {F::PostMut} π pclos clos_state *[acc; e] clos_state' acc' -∗ 
            ClosInv π acc' it_state' clos_state' ∗
            ⌜P (seq ++ [e]) acc'⌝)
        )")]
    #[rr::exists("seq", "s2", "s2'")]
    // We observe a sequence of elements emitted from the iterator.
    #[rr::ensures(#iris "{Inv} π p s2'")]
    #[rr::ensures(#iris "IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq s2")]
    #[rr::ensures(#iris "{Next} π p s2 None s2'")]
    #[rr::ensures("P seq ret")]
    #[rr::ensures(#iris "ty_ghost_drop {Self} π ($# s2')")]
    fn fold<B, F>(mut self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        while let Some(x) = self.next() {
            #[rr::params("init_state")]
            #[rr::inv_vars("self", "accum", "f")]
            #[rr::exists("seq")]
            #[rr::invariant(#iris "IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p init_state seq self")]
            #[rr::invariant(#iris "{Inv} π p self")]
            #[rr::invariant(#iris "ClosInv π accum self f")]  
            #[rr::invariant("P seq accum")]
            #[rr::ignore] || {};
            accum = f(accum, x);
        }
        accum
    }

        /*
    #[rr::params("p", "P" : "list {xt_of Self::Item} → option {xt_of Self::Item} → Prop", "ClosInv" : "thread_id → option {xt_of Self::Item} → {xt_of Self} → {xt_of F} → iProp Σ")]
    #[rr::requires(#iris "{Inv} π p self")]
    #[rr::requires(#iris "ClosInv π init self f")]
    #[rr::requires(#iris "□ (∀ seq acc it_state it_state' clos_state e,
        IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq it_state -∗ 
        {Self::Next} π p it_state (Some e) it_state' -∗
        ClosInv π acc it_state clos_state -∗
        ∃ pclos, {F::Pre} π pclos clos_state *[acc; e] ∗
        {Self::Next} π p it_state (Some e) it_state' ∗ 
        IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq it_state∗ 
        (∀ acc' clos_state', 
            {F::PostMut} π pclos clos_state *[acc; e] clos_state' acc' -∗ 
            ClosInv π acc' it_state' clos_state' ∗
            ⌜P (seq ++ [e]) acc'⌝)
        )")]
    #[rr::exists("seq", "s2", "s2'")]
    // We observe a sequence of elements emitted from the iterator.
    #[rr::ensures(#iris "{Inv} π p s2")]
    #[rr::ensures(#iris "")]
    #[rr::ensures(#iris "IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq s2")]
    #[rr::ensures(#iris "{Next} π p s2 None s2'")]
    #[rr::ensures("P seq ret")]
    #[rr::ensures(#iris "ty_ghost_drop {Self} π ($# s2')")]
    fn reduce<F>(mut self, f: F) -> Option<Self::Item>
    where
        Self: Sized,
        F: FnMut(Self::Item, Self::Item) -> Self::Item,
    {
        let first = self.next()?;
        Some(self.fold(first, f))
    }
        */


    // TODO: more methods
}

#[rr::export_as(core::iter::IntoIterator)]
#[rr::exists("IntoIter" : "{xt_of Self} → {xt_of IntoIter}")]
pub trait IntoIterator {
    /// The type of the elements being iterated over.
    type Item;

    /// Which kind of iterator are we turning this into?
    type IntoIter: Iterator<Item = Self::Item>;

    #[rr::returns("{IntoIter} self")]
    // TODO
    //#[rr::ensures(#iris "{IntoIter::Inv} π ({IntoIter} self)")]
    fn into_iter(self) -> Self::IntoIter;
}

#[rr::instantiate("IntoIter" := "id")]
impl<I> IntoIterator for I where I: Iterator {
    type Item = <I as Iterator>::Item;
    type IntoIter = I;

    #[rr::default_spec]
    fn into_iter(self) -> I {
        self
    }
}


#[rr::export_as(core::iter::FromIterator)]
#[rr::exists("FromSequence" : "list ({xt_of A}) → {xt_of Self}")]
pub trait FromIterator<A> {
    #[rr::verify]
    //#[rr::exists("seq", "s2", "s2'")]
    // Problem: RefinedRust currently does not translate the Iterator requirement on T::IntoIter. 
    // Maybe let's do a hacky wrapper solution for that for now. 
    //#[rr::ensures(#iris "IteratorNextFusedTrans {attrs_of T::IntoIter} ({T::IntoIter} iter) seq s2")]
    //#[rr::ensures(#iris "{T::Next} s2 None s2'")]
    //#[rr::returns("{FromSequence} seq")]
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self;
}
