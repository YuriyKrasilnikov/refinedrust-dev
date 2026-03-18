#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(core_intrinsics)]
#![feature(stmt_expr_attributes)]
#![allow(internal_features)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.cmp")]
#![rr::include("closures")]
#![rr::include("option")]
#![rr::import("rrstd.cmp.theories", "ordering")]

#[repr(i8)]
#[rr::export_as(core::cmp::Ordering)]
#[rr::refined_by("ordering")]
pub enum Ordering {
    #[rr::pattern("Less")]
    Less = -1,
    #[rr::pattern("Equal")]
    Equal = 0,
    #[rr::pattern("Greater")]
    Greater = 1,
}
use Ordering::*;

impl Ordering {
    #[rr::returns("match self with | Less => -1 | Equal => 0 | Greater => 1 end")]
    const fn as_raw(self) -> i8 {
        core::intrinsics::discriminant_value(&self)
    }

    #[rr::returns("bool_decide(self = Equal)")]
    pub const fn is_eq(self) -> bool {
        self.as_raw() == 0
    }

    #[rr::returns ("bool_decide(self ≠ Equal)")] 
    pub const fn is_ne(self) -> bool {
        self.as_raw() != 0
    }

    #[rr::returns("bool_decide(self = Less)")]
    pub const fn is_lt(self) -> bool {
        self.as_raw() < 0
    }

    #[rr::returns("bool_decide(self = Greater)")]
    pub const fn is_gt(self) -> bool {
        self.as_raw() > 0
    }

    #[rr::returns("bool_decide(self ≠ Greater)")]
    pub const fn is_le(self) -> bool {
        self.as_raw() <= 0
    }

    #[rr::returns("bool_decide(self ≠ Less)")]
    pub const fn is_ge(self) -> bool {
        self.as_raw() >= 0
    }
}


// NOTE: we cannot enforce transitivity and symmetry here, as that is an open-world
// requirement that we cannot really enforce locally.
#[rr::export_as(core::cmp::PartialEq)]
#[rr::exists("PEq" : "{xt_of Self} → {xt_of Rhs} → bool")]
pub trait PartialEq<Rhs: ?Sized = Self> {
    #[rr::returns("{PEq} self other")]
    fn eq(&self, other: &Rhs) -> bool;

    #[rr::returns("negb ({PEq} self other)")]
    fn ne(&self, other: &Rhs) -> bool {
        !self.eq(other)
    }
}

#[rr::export_as(core::cmp::Eq)]
#[rr::exists("PEq_refl" : "∀ x : {xt_of Self}, {Self::PEq} x x")]
#[rr::exists("PEq_sym" : "∀ x y : {xt_of Self}, {Self::PEq} x y → {Self::PEq} y x")]
#[rr::exists("PEq_trans" : "∀ x y z: {xt_of Self}, {Self::PEq} x y → {Self::PEq} y z → {Self::PEq} x z")]
/// This is a strong requirement. We should relax this in the future, once we have better setoid
/// automation support in Rocq.
#[rr::exists("PEq_leibniz" : "∀ a b, {Self::PEq} a b ↔ a = b")]
pub trait Eq: PartialEq<Self> {
    // this method is used solely by #[derive(Eq)] to assert
    // that every component of a type implements `Eq`
    // itself. The current deriving infrastructure means doing this
    // assertion without using a method on this trait is nearly
    // impossible.
    //
    // This should never be implemented by hand.
    #[rr::verify]
    fn assert_fields_are_eq(&self) {}
}

#[rr::export_as(core::cmp::PartialOrd)]
#[rr::exists("POrd" : "{xt_of Self} → {xt_of Rhs} → option ordering")]
#[rr::exists("POrd_eq_cons" : "∀ a b, {Self::PEq} a b ↔ {POrd} a b = Some Equal")]
// NOTE: further consistency properties cannot be specified locally
pub trait PartialOrd<Rhs: ?Sized = Self>: PartialEq<Rhs> {
    #[rr::returns("{POrd} self other")]
    fn partial_cmp(&self, other: &Rhs) -> Option<Ordering>;

    // TODO something's broken
    #[rr::trust_me]
    #[rr::returns("bool_decide ({POrd} self other = Some Less)")]
    fn lt(&self, other: &Rhs) -> bool {
        matches!(self.partial_cmp(other), Some(Less))
    }

    #[rr::trust_me]
    #[rr::returns("bool_decide ({POrd} self other = Some Less) || bool_decide ({POrd} self other = Some Equal)")]
    fn le(&self, other: &Rhs) -> bool {
        matches!(self.partial_cmp(other), Some(Less | Equal))
    }

    #[rr::returns("bool_decide ({POrd} self other = Some Greater)")]
    fn gt(&self, other: &Rhs) -> bool {
        matches!(self.partial_cmp(other), Some(Greater))
    }

    #[rr::returns("bool_decide ({POrd} self other = Some Greater) || bool_decide ({POrd} self other = Some Equal)")]
    fn ge(&self, other: &Rhs) -> bool {
        matches!(self.partial_cmp(other), Some(Greater | Equal))
    }
}

#[rr::export_as(core::cmp::Ord)]
#[rr::exists("Ord" : "{xt_of Self} → {xt_of Self} → ordering")]
#[rr::exists("Ord_POrd" : "∀ a b, {Self::POrd} a b = Some ({Ord} a b)")]
#[rr::exists("Ord_lt_trans" : "∀ a b c, a<o{{ {Ord} }} b → b <o{{ {Ord} }} c → a <o{{ {Ord} }} c")]
#[rr::exists("Ord_eq_trans" : "∀ a b c, a=o{{ {Ord} }} b → b =o{{ {Ord} }} c → a =o{{ {Ord} }} c")]
#[rr::exists("Ord_gt_trans" : "∀ a b c, a>o{{ {Ord} }} b → b >o{{ {Ord} }} c → a >o{{ {Ord} }} c")]
#[rr::exists("Ord_antisym" : "∀ a b, a <o{{ {Ord} }} b ↔ b >o{{ {Ord} }} a")]
pub trait Ord: Eq + PartialOrd<Self> {

    #[rr::returns("{Ord} self other")]
    fn cmp(&self, other: &Self) -> Ordering;

    #[rr::returns("if bool_decide ({Ord} self other = Less) then other else self")]
    fn max(self, other: Self) -> Self
        where Self: Sized,
    {
        max_by(self, other, #[rr::only_spec] #[rr::returns("{Self::Ord} a b")] |a, b| Ord::cmp(a, b))
    }

    #[rr::returns("if bool_decide ({Ord} self other = Less) then self else other")]
    fn min(self, other: Self) -> Self
        where Self: Sized,
    {
        min_by(self, other, #[rr::only_spec] #[rr::returns("{Self::Ord} a b")] |a, b| Ord::cmp(a, b))
    }

    #[rr::trust_me]
    fn clamp(self, min: Self, max: Self) -> Self
        where Self: Sized,
    {
        unimplemented!();
        //assert!(min <= max);
        //if self < min {
            //min
        //} else if self > max {
            //max
        //} else {
            //self
        //}
    }
}

#[rr::export_as(core::cmp::max)]
#[rr::returns("if bool_decide ({T::Ord} v1 v2 = Less) then v2 else v1")]
pub fn max<T: Ord>(v1: T, v2: T) -> T {
    v1.max(v2)
}

#[rr::export_as(core::cmp::max_by)]
#[rr::params("p")]
#[rr::requires(#iris "{F::Pre} π p compare *[v2; v1]")]
#[rr::exists("ord")]
#[rr::ensures(#iris "{F::Post} π p compare *[v2; v1] ord")]
#[rr::ensures("ret = if bool_decide(ord = Less) then v1 else v2")]
pub fn max_by<T, F: FnOnce(&T, &T) -> Ordering>(v1: T, v2: T, compare: F) -> T {
    if compare(&v2, &v1).is_lt() { v1 } else { v2 }
}

#[rr::export_as(core::cmp::min)]
#[rr::returns("if bool_decide ({T::Ord} v1 v2 = Less) then v1 else v2")]
pub fn min<T: Ord>(v1: T, v2: T) -> T {
    v1.min(v2)
}

#[rr::export_as(core::cmp::min_by)]
#[rr::params("p")]
#[rr::requires(#iris "{F::Pre} π p compare *[v2; v1]")]
#[rr::exists("ord")]
#[rr::ensures(#iris "{F::Post} π p compare *[v2; v1] ord")]
#[rr::returns("if bool_decide(ord = Less) then v2 else v1")]
pub fn min_by<T, F: FnOnce(&T, &T) -> Ordering>(v1: T, v2: T, compare: F) -> T {
    if compare(&v2, &v1).is_lt() { v2 } else { v1 }
}

macro_rules! partial_eq_impl {
    ($($t:ty)*) => ($(
        #[rr::instantiate("PEq" := "λ a b, bool_decide (a = b)")]
        impl PartialEq for $t {
            fn eq(&self, other: &Self) -> bool { *self == *other }
            fn ne(&self, other: &Self) -> bool { *self != *other }
        }
    )*)
}
partial_eq_impl! {
   // char
    bool usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128
}

macro_rules! eq_impl {
    ($($t:ty)*) => ($(

        #[rr::instantiate("PEq_refl" := #proof "intros ??; solve_goal")]
        #[rr::instantiate("PEq_sym" := #proof "intros ???; solve_goal")]
        #[rr::instantiate("PEq_trans" := #proof "intros ????; solve_goal")]
        #[rr::instantiate("PEq_leibniz" := #proof "intros ???; solve_goal")]
        impl Eq for $t { }
    )*)
}

eq_impl! {
    bool usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128
        //char
}


#[rr::instantiate("PEq" := "λ _ _, true")]
impl PartialEq for () {
    fn eq(&self, _other: &()) -> bool {
        true
    }
    fn ne(&self, _other: &()) -> bool {
        false
    }
}
#[rr::instantiate("PEq_refl" := #proof "intros ??; solve_goal")]
#[rr::instantiate("PEq_sym" := #proof "intros ???; solve_goal")]
#[rr::instantiate("PEq_trans" := #proof "intros ????; solve_goal")]
#[rr::instantiate("PEq_leibniz" := #proof "intros ? [] []; solve_goal")]
impl Eq for () { }

#[rr::instantiate("POrd" := "λ a b, Some Equal")]
#[rr::instantiate("POrd_eq_cons" := #proof "intros ???; solve_goal")]
impl PartialOrd for () {
    fn partial_cmp(&self, _: &()) -> Option<Ordering> {
        Some(Equal)
    }
}

#[rr::instantiate("Ord" := "λ a b, Equal")]
#[rr::instantiate("Ord_POrd" := #proof "intros ???; solve_goal")]
#[rr::instantiate("Ord_lt_trans" := #proof "intros ????; solve_goal")]
#[rr::instantiate("Ord_eq_trans" := #proof "intros ????; solve_goal")]
#[rr::instantiate("Ord_gt_trans" := #proof "intros ????; solve_goal")]
#[rr::instantiate("Ord_antisym" := #proof "intros ? [] []; unfold ord_lt, ord_gt; naive_solver")]
impl Ord for () {
    fn cmp(&self, _other: &()) -> Ordering {
        Equal
    }
}



macro_rules! partial_ord_methods_primitive_impl {
    () => {
        fn lt(&self, other: &Self) -> bool { *self <  *other }
        fn le(&self, other: &Self) -> bool { *self <= *other }
        fn gt(&self, other: &Self) -> bool { *self >  *other }
        fn ge(&self, other: &Self) -> bool { *self >= *other }
    };
}
macro_rules! ord_impl {
    ($($t:ty)*) => ($(
        #[rr::instantiate("POrd" := "λ a b, Some(Z.compare a b)")]
        #[rr::instantiate("POrd_eq_cons" := #proof "intros ???; solve_goal")]
        impl PartialOrd for $t {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(Ord::cmp(self, other))
            }

            partial_ord_methods_primitive_impl!();
        }

        #[rr::instantiate("Ord" := "Z.compare")]
        #[rr::instantiate("Ord_POrd" := #proof "intros ???; solve_goal")]
        #[rr::instantiate("Ord_lt_trans" := #proof "intros ????; solve_goal")]
        #[rr::instantiate("Ord_eq_trans" := #proof "intros ????; solve_goal")]
        #[rr::instantiate("Ord_gt_trans" := #proof "intros ????; solve_goal")]
        #[rr::instantiate("Ord_antisym" := #proof "intros ???; solve_goal")]
        impl Ord for $t {
            fn cmp(&self, other: &Self) -> Ordering {
                if *self < *other {
                    Ordering::Less
                }
                else if *self == *other {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }
        }
    )*)
}

ord_impl! {
    usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128
    //char
}


/*
macro_rules! partial_ord_impl {
    ($($t:ty)*) => ($(
        #[rr::verify]
        impl PartialOrd for $t {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                match (*self <= *other, *self >= *other) {
                    (false, false) => None,
                    (false, true) => Some(Greater),
                    (true, false) => Some(Less),
                    (true, true) => Some(Equal),
                }
            }

            partial_ord_methods_primitive_impl!();
        }
    )*)
}
*/

/*
impl Ord for bool {
    fn cmp(&self, other: &bool) -> Ordering {
        // Casting to i8's and converting the difference to an Ordering generates
        // more optimal assembly.
        // See <https://github.com/rust-lang/rust/issues/66780> for more info.
        match (*self as i8) - (*other as i8) {
            -1 => Less,
            0 => Equal,
            1 => Greater,
            // SAFETY: bool as i8 returns 0 or 1, so the difference can't be anything else
            _ => unsafe { unreachable_unchecked() },
        }
    }

    #[inline]
    fn min(self, other: bool) -> bool {
        self & other
    }

    #[inline]
    fn max(self, other: bool) -> bool {
        self | other
    }

    #[inline]
    fn clamp(self, min: bool, max: bool) -> bool {
        assert!(min <= max);
        self.max(min).min(max)
    }
}


impl PartialOrd for bool {
    #[rr::instantiate("POrd" : "λ a b, if self && ~other then Some Greater else if ~self && other then Some Less else Some Equal")]
    fn partial_cmp(&self, other: &bool) -> Option<Ordering> {
        Some(self.cmp(other))
    }

    partial_ord_methods_primitive_impl!();
}
*/

// & pointers
#[rr::instantiate("PEq" := "{A::PEq}")]
impl<A: ?Sized, B: ?Sized> PartialEq<&B> for &A
where A: PartialEq<B>,
{
    fn eq(&self, other: &&B) -> bool {
        PartialEq::eq(*self, *other)
    }
    fn ne(&self, other: &&B) -> bool {
        PartialEq::ne(*self, *other)
    }
}


#[rr::instantiate("PEq_refl" := #proof "intros ??? ??; simpl; by apply Eq_PEq_refl")]
#[rr::instantiate("PEq_sym" := #proof "intros ??? ??; simpl; by apply Eq_PEq_sym")]
#[rr::instantiate("PEq_trans" := #proof "intros ??? ??; simpl; by apply Eq_PEq_trans")]
#[rr::instantiate("PEq_leibniz" := #proof "intros ??? ??; simpl; by apply Eq_PEq_leibniz")]
impl<A: ?Sized> Eq for &A where A: Eq {}

#[rr::instantiate("POrd" := "λ a b, {A::POrd} a b")]
#[rr::instantiate("POrd_eq_cons" := #proof "intros ??? ????; simpl; apply PartialOrd_POrd_eq_cons")]
impl<A: ?Sized, B: ?Sized> PartialOrd<&B> for &A
where
    A: PartialOrd<B>,
{
    fn partial_cmp(&self, other: &&B) -> Option<Ordering> {
        PartialOrd::partial_cmp(*self, *other)
    }
    fn lt(&self, other: &&B) -> bool {
        PartialOrd::lt(*self, *other)
    }
    fn le(&self, other: &&B) -> bool {
        PartialOrd::le(*self, *other)
    }
    fn gt(&self, other: &&B) -> bool {
        PartialOrd::gt(*self, *other)
    }
    fn ge(&self, other: &&B) -> bool {
        PartialOrd::ge(*self, *other)
    }
}

#[rr::instantiate("Ord" := "λ a b, {A::Ord} a b")]
#[rr::instantiate("Ord_POrd" := #proof "intros ??? ????; simpl; by apply Ord_Ord_POrd")]
#[rr::instantiate("Ord_lt_trans" := #proof "intros ???? ????; simpl; by apply Ord_Ord_lt_trans")]
#[rr::instantiate("Ord_eq_trans" := #proof "intros ???? ????; simpl; by apply Ord_Ord_eq_trans")]
#[rr::instantiate("Ord_gt_trans" := #proof "intros ???? ????; simpl; by apply Ord_Ord_gt_trans")]
#[rr::instantiate("Ord_antisym" := #proof "intros ??? ????; simpl; by apply Ord_Ord_antisym")]
impl<A: ?Sized> Ord for &A
where
    A: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(*self, *other)
    }
}

// &mut pointers
#[rr::instantiate("PEq" := "λ a b, {A::PEq} a.cur b.cur")]
impl<A: ?Sized, B: ?Sized> PartialEq<&mut B> for &mut A
    where A: PartialEq<B>,
{
    fn eq(&self, other: &&mut B) -> bool {
        PartialEq::eq(*self, *other)
    }
    fn ne(&self, other: &&mut B) -> bool {
        PartialEq::ne(*self, *other)
    }
}


#[rr::instantiate("PEq" := "λ a b, {A::PEq} a b.cur")]
impl<A: ?Sized, B: ?Sized> PartialEq<&mut B> for &A
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&mut B) -> bool {
        PartialEq::eq(*self, *other)
    }
    fn ne(&self, other: &&mut B) -> bool {
        PartialEq::ne(*self, *other)
    }
}

#[rr::instantiate("PEq" := "λ a b, {A::PEq} a.cur b")]
impl<A: ?Sized, B: ?Sized> PartialEq<&B> for &mut A
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&B) -> bool {
        PartialEq::eq(*self, *other)
    }
    fn ne(&self, other: &&B) -> bool {
        PartialEq::ne(*self, *other)
    }
}

// TODO: Requiring Leibniz is too strong: we cannot take equality on the borrow variable into
// account
/*
#[rr::instantiate("PEq_refl" := #proof "intros ??? ??; simpl; by apply Eq_PEq_refl")]
#[rr::instantiate("PEq_sym" := #proof "intros ??? ??; simpl; by apply Eq_PEq_sym")]
#[rr::instantiate("PEq_trans" := #proof "intros ??? ??; simpl; by apply Eq_PEq_trans")]
#[rr::instantiate("PEq_leibniz" := #proof "intros ??? ??; simpl; by apply Eq_PEq_leibniz")]
impl<A: ?Sized> Eq for &mut A where A: Eq {}

impl<A: ?Sized, B: ?Sized> const PartialOrd<&mut B> for &mut A
where
    A: PartialOrd<B>,
{
    fn partial_cmp(&self, other: &&mut B) -> Option<Ordering> {
        PartialOrd::partial_cmp(*self, *other)
    }
    fn lt(&self, other: &&mut B) -> bool {
        PartialOrd::lt(*self, *other)
    }
    fn le(&self, other: &&mut B) -> bool {
        PartialOrd::le(*self, *other)
    }
    fn gt(&self, other: &&mut B) -> bool {
        PartialOrd::gt(*self, *other)
    }
    fn ge(&self, other: &&mut B) -> bool {
        PartialOrd::ge(*self, *other)
    }
}
impl<A: ?Sized> const Ord for &mut A
where
    A: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(*self, *other)
    }
}
*/


// Option

// Note: We cannot use `bool_decide` here, as we don't know that `T` is Eq, i.e. that the equality is correct.
#[rr::instantiate("PEq" := "λ a b, match a, b with | Some a, Some b => {T::PEq} a b | None, None => true | _, _ => false end")]
impl<T: PartialEq> PartialEq for Option<T> {
    // TODO: lifetime encoding
    #[rr::trust_me]
    fn eq(&self, other: &Self) -> bool {
        // Spelling out the cases explicitly optimizes better than
        // `_ => false`
        match (self, other) {
            (Some(l), Some(r)) => l.eq(r),
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        }
    }
}

#[rr::instantiate("PEq_refl" := #proof "intros ??? ?[]; simpl; by try apply Eq_PEq_refl")]
#[rr::instantiate("PEq_sym" := #proof "intros ??? ? [] []; simpl; by try apply Eq_PEq_sym")]
#[rr::instantiate("PEq_trans" := #proof "intros ??? ? [] [] []; simpl; by try apply Eq_PEq_trans")]
#[rr::instantiate("PEq_leibniz" := #proof "intros ??? ? [a | ] [b | ]; simpl; [etrans; first apply Eq_PEq_leibniz | ..]; naive_solver")]
impl<T: Eq> Eq for Option<T> { }

#[rr::instantiate("POrd" := "option_partial_cmp {T::POrd}")]
#[rr::instantiate("POrd_eq_cons" := #proof "intros ??? ? [] []; simpl; by try apply PartialOrd_POrd_eq_cons")]
impl<T: PartialOrd> PartialOrd for Option<T> {
    // TODO lifetime encoding
    #[rr::trust_me]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Some(l), Some(r)) => l.partial_cmp(r),
            (Some(_), None) => Some(Ordering::Greater),
            (None, Some(_)) => Some(Ordering::Less),
            (None, None) => Some(Ordering::Equal),
        }
    }
}


#[rr::instantiate("Ord" := "option_cmp {T::Ord}")]
#[rr::instantiate("Ord_POrd" := #proof "intros ?????? [] []; simpl; by try apply Ord_Ord_POrd")]
#[rr::instantiate("Ord_lt_trans" := #proof "intros ?????? [] [] []; simpl; by try apply Ord_Ord_lt_trans")]
#[rr::instantiate("Ord_eq_trans" := #proof "intros ?????? [] [] []; simpl; by try apply Ord_Ord_eq_trans")]
#[rr::instantiate("Ord_gt_trans" := #proof "intros ?????? [] [] []; simpl; by try apply Ord_Ord_gt_trans")]
#[rr::instantiate("Ord_antisym" := #proof "intros ?????? [] []; simpl; by try apply Ord_Ord_antisym")]
impl<T: Ord> Ord for Option<T> {
    #[rr::trust_me]
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Some(l), Some(r)) => l.cmp(r),
            (Some(_), None) => Ordering::Greater,
            (None, Some(_)) => Ordering::Less,
            (None, None) => Ordering::Equal,
        }
    }
}
