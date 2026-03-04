#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.arithops")]


#[rr::export_as(core::ops::Add)]
#[rr::exists("AddOpDefined" : "{xt_of Self} → {xt_of Rhs} → Prop")]
#[rr::exists("AddOp" : "{xt_of Self} → {xt_of Rhs} → {xt_of Output}")]
pub trait Add<Rhs = Self> {
    type Output;

    #[rr::requires("{AddOpDefined} self rhs")]
    #[rr::returns("{AddOp} self rhs")]
    fn add(self, rhs: Rhs) -> Self::Output;
}

macro_rules! add_impl {
    ($t:ty, $x:expr) => (
        #[rr::instantiate("AddOp" := "λ a b : Z, a + b")] 
        #[rr::instantiate("AddOpDefined" := $x)]
        impl Add for $t {
            type Output = $t;

            #[rr::default_spec]
            fn add(self, other: $t) -> $t { self + other }
        }

        #[rr::instantiate("AddOp" := "λ a b : Z, a + b")] 
        #[rr::instantiate("AddOpDefined" := $x)]
        impl Add<$t> for &$t {
            type Output = $t;

            #[rr::default_spec]
            fn add(self, other: $t) -> $t { *self + other }
        }

        #[rr::instantiate("AddOp" := "λ a b : Z, a + b")] 
        #[rr::instantiate("AddOpDefined" := $x)]
        impl<'a> Add<&'a $t> for $t {
            type Output = $t;

            #[rr::default_spec]
            fn add(self, other: &'a $t) -> $t { self + *other }
        }

        #[rr::instantiate("AddOp" := "λ a b : Z, a + b")] 
        #[rr::instantiate("AddOpDefined" := $x)]
        impl<'a> Add<&'a $t> for & $t {
            type Output = $t;

            #[rr::default_spec]
            fn add(self, other: &'a $t) -> $t { *self + *other }
        }
    )
}


add_impl! { usize, "λ a b, (a + b) ∈ usize" }
add_impl! { u8, "λ a b, (a + b) ∈ u8" }
add_impl! { u16, "λ a b, (a + b) ∈ u16" }
add_impl! { u32, "λ a b, (a + b) ∈ u32" }
add_impl! { u64, "λ a b, (a + b) ∈ u64" }
add_impl! { u128, "λ a b, (a + b) ∈ u128" }
add_impl! { isize, "λ a b, (a + b) ∈ isize" }
add_impl! { i8, "λ a b, (a + b) ∈ i8" }
add_impl! { i16, "λ a b, (a + b) ∈ i16" }
add_impl! { i32, "λ a b, (a + b) ∈ i32" }
add_impl! { i64, "λ a b, (a + b) ∈ i64" }
add_impl! { i128, "λ a b, (a + b) ∈ i128" }


#[rr::export_as(core::ops::Mul)]
#[rr::exists("MulOpDefined" : "{xt_of Self} → {xt_of Rhs} → Prop")]
#[rr::exists("MulOp" : "{xt_of Self} → {xt_of Rhs} → {xt_of Output}")]
pub trait Mul<Rhs = Self> {
    type Output;

    #[rr::requires("{MulOpDefined} self rhs")]
    #[rr::returns("{MulOp} self rhs")]
    fn mul(self, rhs: Rhs) -> Self::Output;
}

macro_rules! mul_impl {
    ($t:ty, $x:expr) => (
        #[rr::instantiate("MulOp" := "λ a b : Z, a * b")] 
        #[rr::instantiate("MulOpDefined" := $x)]
        impl Mul for $t {
            type Output = $t;

            #[rr::default_spec]
            fn mul(self, other: $t) -> $t { self * other }
        }

        #[rr::instantiate("MulOp" := "λ a b : Z, a * b")] 
        #[rr::instantiate("MulOpDefined" := $x)]
        impl Mul<$t> for &$t {
            type Output = $t;

            #[rr::default_spec]
            fn mul(self, other: $t) -> $t { *self * other }
        }

        #[rr::instantiate("MulOp" := "λ a b : Z, a * b")] 
        #[rr::instantiate("MulOpDefined" := $x)]
        impl<'a> Mul<&'a $t> for $t {
            type Output = $t;

            #[rr::default_spec]
            fn mul(self, other: &'a $t) -> $t { self * *other }
        }

        #[rr::instantiate("MulOp" := "λ a b : Z, a * b")] 
        #[rr::instantiate("MulOpDefined" := $x)]
        impl<'a> Mul<&'a $t> for & $t {
            type Output = $t;

            #[rr::default_spec]
            fn mul(self, other: &'a $t) -> $t { *self * *other }
        }
    )
}


mul_impl! { usize, "λ a b, (a * b) ∈ usize" }
mul_impl! { u8, "λ a b, (a * b) ∈ u8" }
mul_impl! { u16, "λ a b, (a * b) ∈ u16" }
mul_impl! { u32, "λ a b, (a * b) ∈ u32" }
mul_impl! { u64, "λ a b, (a * b) ∈ u64" }
mul_impl! { u128, "λ a b, (a * b) ∈ u128" }
mul_impl! { isize, "λ a b, (a * b) ∈ isize" }
mul_impl! { i8, "λ a b, (a * b) ∈ i8" }
mul_impl! { i16, "λ a b, (a * b) ∈ i16" }
mul_impl! { i32, "λ a b, (a * b) ∈ i32" }
mul_impl! { i64, "λ a b, (a * b) ∈ i64" }
mul_impl! { i128, "λ a b, (a * b) ∈ i128" }



#[rr::export_as(core::ops::Sub)]
#[rr::exists("SubOpDefined" : "{xt_of Self} → {xt_of Rhs} → Prop")]
#[rr::exists("SubOp" : "{xt_of Self} → {xt_of Rhs} → {xt_of Output}")]
pub trait Sub<Rhs = Self> {
    type Output;

    #[rr::requires("{SubOpDefined} self rhs")]
    #[rr::returns("{SubOp} self rhs")]
    fn sub(self, rhs: Rhs) -> Self::Output;
}

macro_rules! sub_impl {
    ($t:ty, $x:expr) => (
        #[rr::instantiate("SubOp" := "λ a b : Z, a - b")] 
        #[rr::instantiate("SubOpDefined" := $x)]
        impl Sub for $t {
            type Output = $t;

            #[rr::default_spec]
            fn sub(self, other: $t) -> $t { self - other }
        }

        #[rr::instantiate("SubOp" := "λ a b : Z, a - b")] 
        #[rr::instantiate("SubOpDefined" := $x)]
        impl Sub<$t> for &$t {
            type Output = $t;

            #[rr::default_spec]
            fn sub(self, other: $t) -> $t { *self - other }
        }

        #[rr::instantiate("SubOp" := "λ a b : Z, a - b")] 
        #[rr::instantiate("SubOpDefined" := $x)]
        impl<'a> Sub<&'a $t> for $t {
            type Output = $t;

            #[rr::default_spec]
            fn sub(self, other: &'a $t) -> $t { self - *other }
        }

        #[rr::instantiate("SubOp" := "λ a b : Z, a - b")] 
        #[rr::instantiate("SubOpDefined" := $x)]
        impl<'a> Sub<&'a $t> for & $t {
            type Output = $t;

            #[rr::default_spec]
            fn sub(self, other: &'a $t) -> $t { *self - *other }
        }
    )
}


sub_impl! { usize, "λ a b, (a - b) ∈ usize" }
sub_impl! { u8, "λ a b, (a - b) ∈ u8" }
sub_impl! { u16, "λ a b, (a - b) ∈ u16" }
sub_impl! { u32, "λ a b, (a - b) ∈ u32" }
sub_impl! { u64, "λ a b, (a - b) ∈ u64" }
sub_impl! { u128, "λ a b, (a - b) ∈ u128" }
sub_impl! { isize, "λ a b, (a - b) ∈ isize" }
sub_impl! { i8, "λ a b, (a - b) ∈ i8" }
sub_impl! { i16, "λ a b, (a - b) ∈ i16" }
sub_impl! { i32, "λ a b, (a - b) ∈ i32" }
sub_impl! { i64, "λ a b, (a - b) ∈ i64" }
sub_impl! { i128, "λ a b, (a - b) ∈ i128" }


#[rr::export_as(core::ops::AddAssign)]
#[rr::exists("AddAssignOpDefined" : "{xt_of Self} → {xt_of Rhs} → Prop")]
#[rr::exists("AddAssignOp" : "{xt_of Self} → {xt_of Rhs} → {xt_of Self}")]
pub trait AddAssign<Rhs = Self> {

    #[rr::requires("{AddAssignOpDefined} self.cur rhs")]
    #[rr::observe("self.ghost": "{AddAssignOp} self.cur rhs")]
    fn add_assign(&mut self, rhs: Rhs);
}

macro_rules! add_assign_impl {
    ($t:ty, $x:expr) => (
        #[rr::instantiate("AddAssignOp" := "λ a b : Z, a + b")] 
        #[rr::instantiate("AddAssignOpDefined" := $x)]
        impl AddAssign for $t {
            fn add_assign(&mut self, other: $t) { *self += other }
        }

        #[rr::instantiate("AddAssignOp" := "λ a b : Z, a + b")] 
        #[rr::instantiate("AddAssignOpDefined" := $x)]
        impl AddAssign<& $t> for $t {
            fn add_assign(&mut self, other: & $t) {
                Self::add_assign(self, *other);
            }
        }
    )
}


add_assign_impl! { usize, "λ a b, (a + b) ∈ usize" }
add_assign_impl! { u8, "λ a b, (a + b) ∈ u8" }
add_assign_impl! { u16, "λ a b, (a + b) ∈ u16" }
add_assign_impl! { u32, "λ a b, (a + b) ∈ u32" }
add_assign_impl! { u64, "λ a b, (a + b) ∈ u64" }
add_assign_impl! { u128, "λ a b, (a + b) ∈ u128" }
add_assign_impl! { isize, "λ a b, (a + b) ∈ isize" }
add_assign_impl! { i8, "λ a b, (a + b) ∈ i8" }
add_assign_impl! { i16, "λ a b, (a + b) ∈ i16" }
add_assign_impl! { i32, "λ a b, (a + b) ∈ i32" }
add_assign_impl! { i64, "λ a b, (a + b) ∈ i64" }
add_assign_impl! { i128, "λ a b, (a + b) ∈ i128" }


#[rr::export_as(core::ops::SubAssign)]
#[rr::exists("SubAssignOpDefined" : "{xt_of Self} → {xt_of Rhs} → Prop")]
#[rr::exists("SubAssignOp" : "{xt_of Self} → {xt_of Rhs} → {xt_of Self}")]
pub trait SubAssign<Rhs = Self> {

    #[rr::requires("{SubAssignOpDefined} self.cur rhs")]
    #[rr::observe("self.ghost": "{SubAssignOp} self.cur rhs")]
    fn sub_assign(&mut self, rhs: Rhs);
}

macro_rules! sub_assign_impl {
    ($t:ty, $x:expr) => (
        #[rr::instantiate("SubAssignOp" := "λ a b : Z, a - b")] 
        #[rr::instantiate("SubAssignOpDefined" := $x)]
        impl SubAssign for $t {
            fn sub_assign(&mut self, other: $t) { *self -= other }
        }

        #[rr::instantiate("SubAssignOp" := "λ a b : Z, a - b")] 
        #[rr::instantiate("SubAssignOpDefined" := $x)]
        impl SubAssign<& $t> for $t {
            fn sub_assign(&mut self, other: & $t) {
                Self::sub_assign(self, *other);
            }
        }
    )
}


sub_assign_impl! { usize, "λ a b, (a - b) ∈ usize" }
sub_assign_impl! { u8, "λ a b, (a - b) ∈ u8" }
sub_assign_impl! { u16, "λ a b, (a - b) ∈ u16" }
sub_assign_impl! { u32, "λ a b, (a - b) ∈ u32" }
sub_assign_impl! { u64, "λ a b, (a - b) ∈ u64" }
sub_assign_impl! { u128, "λ a b, (a - b) ∈ u128" }
sub_assign_impl! { isize, "λ a b, (a - b) ∈ isize" }
sub_assign_impl! { i8, "λ a b, (a - b) ∈ i8" }
sub_assign_impl! { i16, "λ a b, (a - b) ∈ i16" }
sub_assign_impl! { i32, "λ a b, (a - b) ∈ i32" }
sub_assign_impl! { i64, "λ a b, (a - b) ∈ i64" }
sub_assign_impl! { i128, "λ a b, (a - b) ∈ i128" }


#[rr::export_as(core::ops::MulAssign)]
#[rr::exists("MulAssignOpDefined" : "{xt_of Self} → {xt_of Rhs} → Prop")]
#[rr::exists("MulAssignOp" : "{xt_of Self} → {xt_of Rhs} → {xt_of Self}")]
pub trait MulAssign<Rhs = Self> {

    #[rr::requires("{MulAssignOpDefined} self.cur rhs")]
    #[rr::observe("self.ghost": "{MulAssignOp} self.cur rhs")]
    fn mul_assign(&mut self, rhs: Rhs);
}

macro_rules! mul_assign_impl {
    ($t:ty, $x:expr) => (
        #[rr::instantiate("MulAssignOp" := "λ a b : Z, a * b")] 
        #[rr::instantiate("MulAssignOpDefined" := $x)]
        impl MulAssign for $t {
            fn mul_assign(&mut self, other: $t) { *self *= other }
        }

        #[rr::instantiate("MulAssignOp" := "λ a b : Z, a * b")] 
        #[rr::instantiate("MulAssignOpDefined" := $x)]
        impl MulAssign<& $t> for $t {
            fn mul_assign(&mut self, other: & $t) {
                Self::mul_assign(self, *other);
            }
        }
    )
}


mul_assign_impl! { usize, "λ a b, (a * b) ∈ usize" }
mul_assign_impl! { u8, "λ a b, (a * b) ∈ u8" }
mul_assign_impl! { u16, "λ a b, (a * b) ∈ u16" }
mul_assign_impl! { u32, "λ a b, (a * b) ∈ u32" }
mul_assign_impl! { u64, "λ a b, (a * b) ∈ u64" }
mul_assign_impl! { u128, "λ a b, (a * b) ∈ u128" }
mul_assign_impl! { isize, "λ a b, (a * b) ∈ isize" }
mul_assign_impl! { i8, "λ a b, (a * b) ∈ i8" }
mul_assign_impl! { i16, "λ a b, (a * b) ∈ i16" }
mul_assign_impl! { i32, "λ a b, (a * b) ∈ i32" }
mul_assign_impl! { i64, "λ a b, (a * b) ∈ i64" }
mul_assign_impl! { i128, "λ a b, (a * b) ∈ i128" }


#[rr::export_as(core::ops::Deref)]
#[rr::exists("DerefInto" : "{xt_of Self} → {xt_of Target}")]
pub trait Deref {
    /// The resulting type after dereferencing.
    type Target: ?Sized;

    /// Dereferences the value.
    #[rr::returns("{DerefInto} self")]
    fn deref(&self) -> &Self::Target;
}

#[rr::instantiate("DerefInto" := "id")]
impl<T: ?Sized> Deref for &T {
    type Target = T;

    fn deref(&self) -> &T {
        self
    }
}

#[rr::instantiate("DerefInto" := "λ x, x.cur")]
impl<T: ?Sized> Deref for &mut T {
    type Target = T;

    fn deref(&self) -> &T {
        self
    }
}

#[rr::export_as(core::ops::DerefMut)]
#[rr::exists("DerefMutInject" : "{xt_of Self} → gname → {rt_of Self}")]
pub trait DerefMut: Deref {
    #[rr::exists("γi")]
    #[rr::observe("self.ghost": "{DerefMutInject} self.cur γi")]
    #[rr::returns("({Self::DerefInto} self.cur, γi)")]
    fn deref_mut<'a>(&'a mut self) -> &'a mut Self::Target;
}

// now I get a T. need to produce the new (i,γ) of Self = &mut T. 
// TODO: generate extendlft instructions.
#[rr::only_spec]
#[rr::instantiate("DerefMutInject" := "λ old x, (👻 x, old.ghost)")]
impl<T: ?Sized> DerefMut for &mut T {
    fn deref_mut(&mut self) -> &mut T {
        self
    }
}
