#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![feature(allocator_api)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.alloc")]
#![rr::include("alloc")]
#![rr::include("iterator")]
#![rr::include("option")]
#![rr::include("rr_internal")]
#![rr::include("closures")]
#![rr::include("cmp")]
#![rr::include("index")]
#![rr::include("ptr")]
#![rr::include("ptr_advanced")]

use std::alloc::{Allocator, Global};
use std::marker::PhantomData;
use core::ptr::NonNull;


#[rr::refined_by("xs" : "list (place_rfn {rt_of T})")]
#[rr::exists("x", "y")]
#[rr::export_as(alloc::vec::Vec)]
pub struct Vec<T, A: Allocator = Global> {
    #[rr::field("x")]
    _x: PhantomData<T>,
    #[rr::field("y")]
    _y: A,
}

#[rr::export_as(alloc::vec::Vec)]
#[rr::only_spec]
impl<T> Vec<T> {

    #[rr::returns("[]")]
    pub fn new() -> Self {
        unreachable!();
    }

    #[rr::params("cap")]
    #[rr::args("cap")]
    #[rr::requires("(size_of_array_in_bytes {st_of T} (Z.to_nat cap) ≤ MaxInt ISize)%Z")]
    #[rr::returns("[]")]
    pub fn with_capacity(capacity: usize) -> Self {
        unimplemented!();
    }
}

#[rr::export_as(alloc::vec::Vec)]
#[rr::only_spec]
impl<T, A: Allocator> Vec<T, A> {

    #[rr::params("xs")]
    #[rr::args("xs")]
    #[rr::returns("length xs")]
    pub fn len(&self) -> usize {
        unreachable!();
    }

    #[rr::params("xs", "γ", "x")]
    #[rr::args("(xs, γ)", "x")]
    #[rr::requires("(length xs < MaxInt USize)%Z")]
    #[rr::requires("(size_of_array_in_bytes {st_of T} (2 * length xs) ≤ MaxInt ISize)%Z")]
    #[rr::observe("γ": "<$#> (xs ++ [ x])")]
    pub fn push(&mut self, elem: T) {
        unreachable!();
    }

    #[rr::params("xs", "γ")]
    #[rr::args("(xs, γ)")]
    #[rr::returns("(last xs)")]
    #[rr::observe("γ": "take (length xs - 1) (<$#> xs)")]
    pub fn pop(&mut self) -> Option<T> {
        unreachable!();
    }

    #[rr::params("xs", "γ", "i" : "nat", "x")]
    #[rr::args("(xs, γ)", "Z.of_nat i", "x")]
    #[rr::requires("i ≤ length xs")]
    #[rr::requires("(length xs < MaxInt USize)%Z")]
    #[rr::requires("(size_of_array_in_bytes {st_of T} (2 * length xs) ≤ MaxInt ISize)%Z")]
    #[rr::observe("γ": "<$#> ((take i xs) ++ [x] ++ (drop i xs))")]
    pub fn insert(&mut self, index: usize, elem: T) {
        unreachable!();
    }

    #[rr::params("xs", "γ", "i" : "nat")]
    #[rr::args("(xs, γ)", "Z.of_nat i")]
    #[rr::requires("i < length xs")]
    #[rr::observe("γ": "delete i (<$#> xs)")]
    pub fn remove(&mut self, index: usize) -> T {
        unreachable!(); 
    }

    #[rr::params("xs", "γ", "i" : "nat")]
    #[rr::args("(xs, γ)", "Z.of_nat i")]
    #[rr::requires("i < length xs")]
    #[rr::exists("γi")]
    #[rr::returns("((xs !!! i), γi)")]
    #[rr::observe("γ": "<[i := PlaceGhost γi]> (<$#>  xs)")]
    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        unreachable!(); 
    }

    #[rr::params("xs", "γ", "i" : "nat")]
    #[rr::args("(xs, γ)", "Z.of_nat i")]
    #[rr::exists("γi")]
    #[rr::returns("if decide (i < length xs) then Some (xs !!! i, γi) else None")]
    #[rr::observe("γ": "if decide (i < length xs) then <[i := PlaceGhost γi]> (<$#> xs) else <$#> xs")]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        unreachable!(); 
    }

    #[rr::params("xs", "i" : "nat")]
    #[rr::args("xs", "Z.of_nat i")]
    #[rr::requires("i < length xs")]
    #[rr::returns("(xs !!! i)")]
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        unreachable!(); 
    }

    #[rr::params("xs", "i" : "nat")]
    #[rr::args("xs", "Z.of_nat i")]
    #[rr::returns("if decide (i < length xs) then Some (xs !!! i) else None")]
    pub fn get(&self, index: usize) -> Option<&T> {
        unreachable!();
    }

}

#[rr::export_as(alloc::vec::Vec)]
impl<T, A: Allocator> Vec<T, A> {
    #[rr::returns("bool_decide (self = [])")]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}


#[rr::instantiate("FromSequence" := "λ x, x")]
impl<T> FromIterator<T> for Vec<T> {
    #[rr::only_spec]
    #[rr::default_spec]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Vec<T> {
        unimplemented!();
        //<Self as SpecFromIter<T, I::IntoIter>>::from_iter(iter.into_iter())
    }
}

#[rr::refined_by("xs" : "list ({rt_of T})")]
#[rr::exists("x", "y")]
#[rr::export_as(alloc::vec::into_iter::IntoIter)]
pub struct IntoIter<
    T,
    A: Allocator = Global,
> {
    #[rr::field("x")]
    _x: PhantomData<T>,
    #[rr::field("y")]
    _y: A,
}

#[rr::instantiate("IntoIter" := "id")]
impl<T, A: Allocator> IntoIterator for Vec<T, A> {
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    #[rr::only_spec]
    #[rr::default_spec]
    fn into_iter(self) -> Self::IntoIter {
        unimplemented!();
    }
}

#[rr::instantiate("Next" := "λ π l e l2, 
    (⌜if_None e (l = [] ∧ l2 = [])⌝∗
    ⌜if_Some e (λ e, l = e :: l2)⌝)%I")]
#[rr::instantiate("Inv" := "λ π self, True%I")]
impl<T, A: Allocator> Iterator for IntoIter<T, A> {
    type Item = T;

    #[rr::only_spec]
    #[rr::default_spec]
    fn next(&mut self) -> Option<T> {
        unimplemented!();
    }
}


/*
#[rr::export_as(alloc::vec::Vec)]
#[rr::only_spec]
impl<T, A: Allocator> Vec<T, A> {
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, A>
    where
        R: RangeBounds<usize>,
    {
        // very funky implementation...
        unreachable!();
    }
}

// refine by the sequence of elements it will emit.
// on drop: update to the vector.
pub struct Drain<
    'a,
    T: 'a,
    A: Allocator + 'a = Global,
> {
    /// Index of tail to preserve
    tail_start: usize,
    /// Length of tail
    tail_len: usize,
    /// Current remaining range to remove
    iter: slice::Iter<'a, T>,
    vec: NonNull<Vec<T, A>>,
}


impl<T, A: Allocator> Iterator for Drain<'_, T, A> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        unimplemented!();
        //self.iter.next().map(|elt| unsafe { ptr::read(elt as *const _) })
    }
}
*/






mod private_slice_index {
    #[rr::export_as(core::slice::index::private_slice_index::SliceIndex)]
    pub trait Sealed {}

    impl Sealed for usize {}
}



#[rr::export_as(core::slice::index::SliceIndex)]
#[rr::exists("SliceIndexProj" : "{xt_of T} → {xt_of Self} → option {xt_of Output}")]
#[rr::exists("SliceIndexInj" : "{xt_of T} → {xt_of Self} → gname → {rt_of T}")]
pub unsafe trait SliceIndex<T: ?Sized>: private_slice_index::Sealed {
    /// The output type returned by methods.
    type Output: ?Sized;

    /// Returns a shared reference to the output at this location, if in
    /// bounds.
    #[rr::returns("{SliceIndexProj} slice self")]
    fn get(self, slice: &T) -> Option<&Self::Output>;

    /// Returns a mutable reference to the output at this location, if in
    /// bounds.
    #[rr::exists("γi")]
    #[rr::returns("fmap (λ x, (x, γi)) ({SliceIndexProj} slice.cur self)")]
    #[rr::observe("slice.ghost": "if {SliceIndexProj} slice.cur self then {SliceIndexInj} slice.cur self γi else $#@{{ {rt_of T} }} slice.cur")]
    fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;

    /* TODO: unclear what is a good specification
    /// Returns a pointer to the output at this location, without
    /// performing any bounds checking.
    ///
    /// Calling this method with an out-of-bounds index or a dangling `slice` pointer
    /// is *[undefined behavior]* even if the resulting pointer is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    unsafe fn get_unchecked(self, slice: *const T) -> *const Self::Output;

    /// Returns a mutable pointer to the output at this location, without
    /// performing any bounds checking.
    ///
    /// Calling this method with an out-of-bounds index or a dangling `slice` pointer
    /// is *[undefined behavior]* even if the resulting pointer is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    unsafe fn get_unchecked_mut(self, slice: *mut T) -> *mut Self::Output;
    */

    /// Returns a shared reference to the output at this location, panicking
    /// if out of bounds.
    #[rr::ensures("Some ret = {SliceIndexProj} slice self")]
    fn index(self, slice: &T) -> &Self::Output;

    /// Returns a mutable reference to the output at this location, panicking
    /// if out of bounds.
    #[rr::exists("γi", "ret")]
    #[rr::ensures("Some ret = {SliceIndexProj} slice.cur self")]
    #[rr::returns("(ret, γi)")] 
    #[rr::observe("slice.ghost": "{SliceIndexInj} slice.cur self γi")]
    fn index_mut(self, slice: &mut T) -> &mut Self::Output;
}

/*
#[rr::instantiate("SliceIndexProj" := "λ slice i, slice !! (Z.to_nat i)")]
#[rr::instantiate("SliceIndexInj" := "λ slice i γ, <[Z.to_nat i := PlaceGhost γ]> ($# slice)")]
unsafe impl<T> SliceIndex<[T]> for usize {
    type Output = T;

    #[rr::default_spec]
    #[rr::only_spec]
    fn get(self, slice: &[T]) -> Option<&T> {
        unimplemented!();
        /*
        if self < slice.len() {
            // SAFETY: `self` is checked to be in bounds.
            unsafe { Some(slice_get_unchecked(slice, self)) }
        } else {
            None
        }
        */
    }

    #[rr::default_spec]
    #[rr::only_spec]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut T> {
        unimplemented!();
        /*
        if self < slice.len() {
            // SAFETY: `self` is checked to be in bounds.
            unsafe { Some(slice_get_unchecked(slice, self)) }
        } else {
            None
        }
        */
    }

    #[rr::default_spec]
    #[rr::only_spec]
    fn index(self, slice: &[T]) -> &T {
        unimplemented!();
        // N.B., use intrinsic indexing
        //&(*slice)[self]
    }

    #[rr::default_spec]
    #[rr::only_spec]
    fn index_mut(self, slice: &mut [T]) -> &mut T {
        unimplemented!();
        // N.B., use intrinsic indexing
        //&mut (*slice)[self]
    }
}














// Index impl for slice
#[rr::instantiate("IndexProj" := "λ self index, self !!! index")]
impl<T, I> Index<I> for [T]
where
    I: SliceIndex<[T]>,
{
    type Output = I::Output;

    #[rr::default_spec]
    #[rr::only_spec]
    fn index(&self, index: I) -> &I::Output {
        index.index(self)
    }
}


impl<T, I> const ops::IndexMut<I> for [T]
where
    I: [const] SliceIndex<[T]>,
{
    #[inline(always)]
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        index.index_mut(self)
    }
}


// Index impl for Vec
impl<T, I: SliceIndex<[T]>, A: Allocator> Index<I> for Vec<T, A> {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        Index::index(&**self, index)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, I: SliceIndex<[T]>, A: Allocator> IndexMut<I> for Vec<T, A> {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        IndexMut::index_mut(&mut **self, index)
    }
}

*/


/*
impl<T, A: Allocator> ops::Deref for Vec<T, A> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> ops::DerefMut for Vec<T, A> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}
*/

// Slice iter 
#[rr::export_as(core::slice::iter::Iter)]
#[rr::refined_by("xs" : "list ({rt_of T})")]
#[rr::exists("x", "y")]
pub struct Iter<'a, T: 'a> {
    /// The pointer to the next element to return, or the past-the-end location
    /// if the iterator is empty.
    ///
    /// This address will be used for all ZST elements, never changed.
    //ptr: NonNull<T>,
    /// For non-ZSTs, the non-null pointer to the past-the-end element.
    ///
    /// For ZSTs, this is `ptr::without_provenance_mut(len)`.
    #[rr::field("x")]
    end_or_len: *const T,
    #[rr::field("y")]
    _marker: PhantomData<&'a T>,
}

#[rr::instantiate("Next" := "λ π l e l2, 
    (⌜if_None e (l = [] ∧ l2 = [])⌝∗
    ⌜if_Some e (λ e, l = e :: l2)⌝)%I")]
#[rr::instantiate("Inv" := "λ π self, True%I")]
impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[rr::only_spec]
    fn next(&mut self) -> Option<&'a T> {
        unimplemented!();
    }

    #[rr::only_spec]
    fn position<F>(&mut self, f: F) -> Option<usize>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        unimplemented!();
    }

    #[rr::only_spec]
    fn all<F>(&mut self, f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        unimplemented!();
    }
}

// Slice IterMut
#[rr::export_as(core::slice::iter::IterMut)]
#[rr::refined_by("xs" : "(list ({rt_of T} * gname))%type")]
// Ownership: Uniq 'a xs.1 ownership of the array elements (big sep)
#[rr::exists("x" : "loc", "y" : "loc")]
pub struct IterMut<'a, T: 'a> {
    /// The pointer to the next element to return, or the past-the-end location
    /// if the iterator is empty.
    ///
    /// This address will be used for all ZST elements, never changed.
    #[rr::field("x")]
    ptr: NonNull<T>,
    /// For non-ZSTs, the non-null pointer to the past-the-end element.
    ///
    /// For ZSTs, this is `ptr::without_provenance_mut(len)`.
    #[rr::field("y")]
    end_or_len: *mut T,
    #[rr::field("tt")]
    _marker: PhantomData<&'a mut T>,
}

#[rr::instantiate("Next" := "λ π l1 e l2, 
    (⌜if_None e (l1 = [] ∧ l2 = [])⌝ ∗
    ⌜if_Some e (λ e, l1 = e :: l2)⌝)%I")]
#[rr::instantiate("Inv" := "λ π self, True%I")]
impl<'a, T: 'a> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    // when verifying this, we need to make sure to use the right ghost var.
    // otherwise, close Next under RelEq
    #[rr::only_spec]
    fn next(&mut self) -> Option<&'a mut T> {
        unimplemented!();
    }

    //#[rr::only_spec]
    //fn position<F>(&mut self, f: F) -> Option<usize>
    //where
        //Self: Sized,
        //F: FnMut(Self::Item) -> bool,
    //{
        //unimplemented!();
    //}
}

#[rr::only_spec]
#[rr::exists("γs")]
#[rr::ensures("length γs = length x.cur")]
#[rr::observe("x.ghost": "(PlaceGhost <$> γs) : list (place_rfn {rt_of T})")]
#[rr::returns("zip x.cur γs")]
fn vec_iter_mut<T>(x: &mut Vec<T>) -> IterMut<'_, T> {
    unimplemented!();
}

// TODO: add ghost drop instance to get remaining observations


// To make this useful, we need to gather up the observations, maybe into a bigsep.
// Obs list or so? 
// Easier to resolve at resolve_ghost using the vector instance or to have a Rel? 
// I guess for resolve_ghost_iter we can just check for the ObsList in the context and have an easy
// time.
//
