#![rr::import("rrstd.iterator.theories", "step")]

#![rr::include("clone")]
#![rr::include("cmp")]
#![rr::include("option")]
#![rr::include("range")]

use crate::traits::iterator::*;

// TODO: What is a good semantic interpretation for this?
// I should make sure that the properties become part of the safety contract.
// I guess maybe that means that the attrs become part of the semantic interp.
#[rr::export_as(core::iter::TrustedStep)]
pub unsafe trait TrustedStep: Step + Copy {}

#[rr::export_as(core::iter::Step)]
#[rr::exists("Forward" : "{xt_of Self} → nat → option {xt_of Self}")]
#[rr::exists("Backward" : "{xt_of Self} → nat → option {xt_of Self}")]
#[rr::exists("StepsBetween" : "{xt_of Self} → {xt_of Self} → plist (RT_xt ∘ place_rfnRT) [ZRT; optionRT ZRT]")] 
pub trait Step: Clone + PartialOrd + Sized {
    #[rr::returns("{StepsBetween} start last")]
    fn steps_between(start: &Self, last: &Self) -> (usize, Option<usize>);

    #[rr::returns("{Forward} start (Z.to_nat count)")]
    fn forward_checked(start: Self, count: usize) -> Option<Self>;

    #[rr::only_spec]
    #[rr::params("n")]
    #[rr::requires("{Forward} start (Z.to_nat count) = Some n")]
    #[rr::returns("n")]
    fn forward(start: Self, count: usize) -> Self {
        unimplemented!();
        //Step::forward_checked(start, count).expect("overflow in `Step::forward`")
    }

    #[rr::only_spec]
    #[rr::params("n")]
    #[rr::requires("{Forward} start (Z.to_nat count) = Some n")]
    #[rr::returns("n")]
    unsafe fn forward_unchecked(start: Self, count: usize) -> Self {
        Step::forward(start, count)
    }

    #[rr::returns("{Backward} start (Z.to_nat count)")]
    fn backward_checked(start: Self, count: usize) -> Option<Self>;

    #[rr::only_spec]
    #[rr::params("n")]
    #[rr::requires("{Backward} start (Z.to_nat count) = Some n")]
    #[rr::returns("n")]
    fn backward(start: Self, count: usize) -> Self {
        unimplemented!();
        //Step::backward_checked(start, count).expect("overflow in `Step::backward`")
    }

    #[rr::only_spec]
    #[rr::params("n")]
    #[rr::requires("{Backward} start (Z.to_nat count) = Some n")]
    #[rr::returns("n")]
    unsafe fn backward_unchecked(start: Self, count: usize) -> Self {
        Step::backward(start, count)
    }
}

macro_rules! step_integer_narrow_impls {
    ($u_narrower:ident, $i_narrower:ident, $u_forward:expr, $u_backward:expr, $i_forward:expr, $i_backward:expr) => {
            #[rr::instantiate("Forward" := $u_forward)]
            #[rr::instantiate("Backward" := $u_backward)]
            #[rr::instantiate("StepsBetween" := "λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]")]
            impl Step for $u_narrower {
                #[rr::default_spec]
                #[rr::trust_me]
                //#[rr::tactics("all: apply wrap_to_it_id; split; unsafe_unfold_common_caesium_defs; solve_goal.")]
                fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
                    if *start <= *end {
                        // This relies on $u_narrower <= usize
                        let steps = (*end - *start) as usize;
                        (steps, Some(steps))
                    } else {
                        (0, None)
                    }
                }

                #[rr::default_spec]
                #[rr::only_spec]
                fn forward_checked(start: Self, n: usize) -> Option<Self> {
                    match Self::try_from(n) {
                        Ok(n) => start.checked_add(n),
                        Err(_) => None, // if n is out of range, `unsigned_start + n` is too
                    }
                }

                #[rr::default_spec]
                #[rr::only_spec]
                fn backward_checked(start: Self, n: usize) -> Option<Self> {
                    match Self::try_from(n) {
                        Ok(n) => start.checked_sub(n),
                        Err(_) => None, // if n is out of range, `unsigned_start - n` is too
                    }
                }
            }

            #[rr::instantiate("Forward" := $i_forward)]
            #[rr::instantiate("Backward" := $i_backward)]
            #[rr::instantiate("StepsBetween" := "λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]")]
            impl Step for $i_narrower {
                #[rr::only_spec]
                #[rr::default_spec]
                fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
                    if *start <= *end {
                        // This relies on $i_narrower <= usize
                        //
                        // Casting to isize extends the width but preserves the sign.
                        // Use wrapping_sub in isize space and cast to usize to compute
                        // the difference that might not fit inside the range of isize.
                        let steps = (*end as isize).wrapping_sub(*start as isize) as usize;
                        (steps, Some(steps))
                    } else {
                        (0, None)
                    }
                }

                #[rr::default_spec]
                #[rr::only_spec]
                fn forward_checked(start: Self, n: usize) -> Option<Self> {
                    match $u_narrower::try_from(n) {
                        Ok(n) => {
                            // Wrapping handles cases like
                            // `Step::forward(-120_i8, 200) == Some(80_i8)`,
                            // even though 200 is out of range for i8.
                            let wrapped = start.wrapping_add(n as Self);
                            if wrapped >= start {
                                Some(wrapped)
                            } else {
                                None // Addition overflowed
                            }
                        }
                        // If n is out of range of e.g. u8,
                        // then it is bigger than the entire range for i8 is wide
                        // so `any_i8 + n` necessarily overflows i8.
                        Err(_) => None,
                    }
                }

                #[rr::default_spec]
                #[rr::only_spec]
                fn backward_checked(start: Self, n: usize) -> Option<Self> {
                    match $u_narrower::try_from(n) {
                        Ok(n) => {
                            // Wrapping handles cases like
                            // `Step::forward(-120_i8, 200) == Some(80_i8)`,
                            // even though 200 is out of range for i8.
                            let wrapped = start.wrapping_sub(n as Self);
                            if wrapped <= start {
                                Some(wrapped)
                            } else {
                                None // Subtraction overflowed
                            }
                        }
                        // If n is out of range of e.g. u8,
                        // then it is bigger than the entire range for i8 is wide
                        // so `any_i8 - n` necessarily overflows i8.
                        Err(_) => None,
                    }
                }
            }
    };
}

step_integer_narrow_impls!{ usize, isize, 
    "λ a b, if bool_decide (a + b ∈ usize) then Some (a + b) else None", "λ a b, if bool_decide (a - b ∈ usize) then Some (a - b) else None",
    "λ a b, if bool_decide (a + b ∈ isize) then Some (a + b) else None", "λ a b, if bool_decide (a - b ∈ isize) then Some (a - b) else None"
}

step_integer_narrow_impls!{ u64, i64, 
    "λ a b, if bool_decide (a + b ∈ u64) then Some (a + b) else None", "λ a b, if bool_decide (a - b ∈ u64) then Some (a - b) else None",
    "λ a b, if bool_decide (a + b ∈ i64) then Some (a + b) else None", "λ a b, if bool_decide (a - b ∈ i64) then Some (a - b) else None"
}

step_integer_narrow_impls!{ u32, i32, 
    "λ a b, if bool_decide (a + b ∈ u32) then Some (a + b) else None", "λ a b, if bool_decide (a - b ∈ u32) then Some (a - b) else None",
    "λ a b, if bool_decide (a + b ∈ i32) then Some (a + b) else None", "λ a b, if bool_decide (a - b ∈ i32) then Some (a - b) else None"
}

step_integer_narrow_impls!{ u16, i16, 
    "λ a b, if bool_decide (a + b ∈ u16) then Some (a + b) else None", "λ a b, if bool_decide (a - b ∈ u16) then Some (a - b) else None",
    "λ a b, if bool_decide (a + b ∈ i16) then Some (a + b) else None", "λ a b, if bool_decide (a - b ∈ i16) then Some (a - b) else None"
}

step_integer_narrow_impls!{ u8, i8, 
    "λ a b, if bool_decide (a + b ∈ u8) then Some (a + b) else None", "λ a b, if bool_decide (a - b ∈ u8) then Some (a - b) else None",
    "λ a b, if bool_decide (a + b ∈ i8) then Some (a + b) else None", "λ a b, if bool_decide (a - b ∈ i8) then Some (a - b) else None"
}


macro_rules! step_integer_wide_impls {
    ($u_wider:ident, $i_wider:ident, $u_forward:expr, $u_backward:expr, $i_forward:expr, $i_backward:expr) => {
            #[rr::instantiate("Forward" := $u_forward)]
            #[rr::instantiate("Backward" := $u_backward)]
            #[rr::instantiate("StepsBetween" := "λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]")]
            impl Step for $u_wider {

                #[rr::default_spec]
                #[rr::only_spec]
                fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
                    if *start <= *end {
                        if let Ok(steps) = usize::try_from(*end - *start) {
                            (steps, Some(steps))
                        } else {
                            (usize::MAX, None)
                        }
                    } else {
                        (0, None)
                    }
                }

                #[rr::default_spec]
                #[rr::only_spec]
                fn forward_checked(start: Self, n: usize) -> Option<Self> {
                    start.checked_add(n as Self)
                }

                #[rr::default_spec]
                #[rr::only_spec]
                fn backward_checked(start: Self, n: usize) -> Option<Self> {
                    start.checked_sub(n as Self)
                }
            }

            #[rr::instantiate("Forward" := $i_forward)]
            #[rr::instantiate("Backward" := $i_backward)]
            #[rr::instantiate("StepsBetween" := "λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]")]
            impl Step for $i_wider {

                #[rr::default_spec]
                #[rr::only_spec]
                fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
                    if *start <= *end {
                        match end.checked_sub(*start) {
                            Some(result) => {
                                if let Ok(steps) = usize::try_from(result) {
                                    (steps, Some(steps))
                                } else {
                                    (usize::MAX, None)
                                }
                            }
                            // If the difference is too big for e.g. i128,
                            // it's also gonna be too big for usize with fewer bits.
                            None => (usize::MAX, None),
                        }
                    } else {
                        (0, None)
                    }
                }

                #[rr::default_spec]
                #[rr::only_spec]
                fn forward_checked(start: Self, n: usize) -> Option<Self> {
                    start.checked_add(n as Self)
                }

                #[rr::default_spec]
                #[rr::only_spec]
                fn backward_checked(start: Self, n: usize) -> Option<Self> {
                    start.checked_sub(n as Self)
                }
            }
};
}

step_integer_wide_impls!{ u128, i128, 
    "λ a b, if bool_decide (a + b ∈ i128) then Some (a + b) else None", "λ a b, if bool_decide (a - b ∈ u128) then Some (a - b) else None",
    "λ a b, if bool_decide (a + b ∈ i128) then Some (a + b) else None", "λ a b, if bool_decide (a - b ∈ i128) then Some (a - b) else None"
}


macro_rules! unsafe_impl_trusted_step {
    ($($type:ty)*) => {$(
        unsafe impl TrustedStep for $type {}
    )*};
}
unsafe_impl_trusted_step![
    //AsciiChar char 
    i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize 
    //Ipv4Addr Ipv6Addr
];

/*
trait RangeIteratorImpl {
    type Item;

    // Iterator
    fn spec_next(&mut self) -> Option<Self::Item>;
    fn spec_nth(&mut self, n: usize) -> Option<Self::Item>;
    fn spec_advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>>;

    // DoubleEndedIterator
    fn spec_next_back(&mut self) -> Option<Self::Item>;
    fn spec_nth_back(&mut self, n: usize) -> Option<Self::Item>;
    fn spec_advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>>;
}

impl<A: Step> RangeIteratorImpl for ops::Range<A> {
    type Item = A;

    #[inline]
    default fn spec_next(&mut self) -> Option<A> {
        if self.start < self.end {
            let n =
                Step::forward_checked(self.start.clone(), 1).expect("`Step` invariants not upheld");
            Some(mem::replace(&mut self.start, n))
        } else {
            None
        }
    }

    #[inline]
    default fn spec_nth(&mut self, n: usize) -> Option<A> {
        if let Some(plus_n) = Step::forward_checked(self.start.clone(), n) {
            if plus_n < self.end {
                self.start =
                    Step::forward_checked(plus_n.clone(), 1).expect("`Step` invariants not upheld");
                return Some(plus_n);
            }
        }

        self.start = self.end.clone();
        None
    }

    #[inline]
    default fn spec_advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        let steps = Step::steps_between(&self.start, &self.end);
        let available = steps.1.unwrap_or(steps.0);

        let taken = available.min(n);

        self.start =
            Step::forward_checked(self.start.clone(), taken).expect("`Step` invariants not upheld");

        NonZero::new(n - taken).map_or(Ok(()), Err)
    }

    #[inline]
    default fn spec_next_back(&mut self) -> Option<A> {
        if self.start < self.end {
            self.end =
                Step::backward_checked(self.end.clone(), 1).expect("`Step` invariants not upheld");
            Some(self.end.clone())
        } else {
            None
        }
    }

    #[inline]
    default fn spec_nth_back(&mut self, n: usize) -> Option<A> {
        if let Some(minus_n) = Step::backward_checked(self.end.clone(), n) {
            if minus_n > self.start {
                self.end =
                    Step::backward_checked(minus_n, 1).expect("`Step` invariants not upheld");
                return Some(self.end.clone());
            }
        }

        self.end = self.start.clone();
        None
    }

    #[inline]
    default fn spec_advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        let steps = Step::steps_between(&self.start, &self.end);
        let available = steps.1.unwrap_or(steps.0);

        let taken = available.min(n);

        self.end =
            Step::backward_checked(self.end.clone(), taken).expect("`Step` invariants not upheld");

        NonZero::new(n - taken).map_or(Ok(()), Err)
    }
}
*/

#[rr::instantiate("Params" := "unit")]
#[rr::instantiate("Next" := "λ π _ s1 e s2, ⌜s1.2 = s2.2 ∧ 
    if_None e (s1 = s2 ∧ s1.1 = s1.2) ∧ 
    if_Some e (λ e, s1.1 = e ∧ Some s2.1 = ({A::Forward} s1.1 1)%nat ∧ {A::POrd} s1.1 s1.2 = Some Less)⌝%I")]
#[rr::instantiate("Inv" := "λ π _ s, True%I")]
impl<A: Step> Iterator for std::ops::Range<A> {
    type Item = A;

    #[rr::default_spec]
    #[rr::trust_me]
    fn next(&mut self) -> Option<A> {
        unimplemented!();
        //self.spec_next()
    }

    /*
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.start < self.end {
            Step::steps_between(&self.start, &self.end)
        } else {
            (0, Some(0))
        }
    }

    #[inline]
    fn count(self) -> usize {
        if self.start < self.end {
            Step::steps_between(&self.start, &self.end).1.expect("count overflowed usize")
        } else {
            0
        }
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<A> {
        self.spec_nth(n)
    }

    #[inline]
    fn last(mut self) -> Option<A> {
        self.next_back()
    }

    #[inline]
    fn min(mut self) -> Option<A>
    where
        A: Ord,
    {
        self.next()
    }

    #[inline]
    fn max(mut self) -> Option<A>
    where
        A: Ord,
    {
        self.next_back()
    }

    #[inline]
    fn is_sorted(self) -> bool {
        true
    }

    #[inline]
    fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        self.spec_advance_by(n)
    }

    #[inline]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        // SAFETY: The TrustedRandomAccess contract requires that callers only pass an index
        // that is in bounds.
        // Additionally Self: TrustedRandomAccess is only implemented for Copy types
        // which means even repeated reads of the same index would be safe.
        unsafe { Step::forward_unchecked(self.start.clone(), idx) }
    }
    */
}
