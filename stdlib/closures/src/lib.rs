#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.closures")]

// NOTE: Our translation of trait requirements erases `Tuple` requirements.
#[rr::export_as(core::marker::Tuple)]
pub trait Tuple { }

#[rr::export_as(core::ops::FnOnce)]
#[rr::exists("Params" : "Type")]
#[rr::exists("Pre" : "thread_id → {Params} → {xt_of Self} → {xt_of Args} → iProp Σ")]
#[rr::exists("Post" : "thread_id → {Params} → {xt_of Self} → {xt_of Args} → {xt_of Output} → iProp Σ")]
// Note: the relation gets both the current and the next state
#[rr::exists("PostMut" : "thread_id → {Params} → {xt_of Self} → {xt_of Args} → {xt_of Self} → {xt_of Output} → iProp Σ")]
#[rr::nondependent]
pub trait FnOnce<Args> {
    /// The returned type after the call operator is used.
    type Output;

    /// Performs the call operation.
    #[rr::params("p")]
    #[rr::requires(#iris "{Pre} π p self args")]
    #[rr::ensures(#iris "{Post} π p self args ret")]
    fn call_once(self, args: Args) -> Self::Output;
}

#[rr::export_as(core::ops::FnMut)]
#[rr::nondependent]
pub trait FnMut<Args>: FnOnce<Args> {
    /// Performs the call operation.
    #[rr::params("p")]
    #[rr::requires(#iris "{Self::Pre} π p self.cur args")]
    #[rr::exists("m'")]
    #[rr::ensures(#iris "{Self::PostMut} π p self.cur args m' ret")]
    #[rr::observe("self.ghost": "$# m'")]
    fn call_mut(&mut self, args: Args) -> Self::Output;
}

#[rr::export_as(core::ops::Fn)]
#[rr::nondependent]
pub trait Fn<Args>: FnMut<Args> {
    /// Performs the call operation.
    #[rr::params("p")]
    #[rr::requires(#iris "{Self::Pre} π p self args")]
    #[rr::ensures(#iris "{Self::Post} π p self args ret")]
    fn call(&self, args: Args) -> Self::Output;
}


impl<A, F: ?Sized> Fn<A> for &F
where
    F: Fn<A>,
{
    #[rr::default_spec]
    #[rr::only_spec]
    fn call(&self, args: A) -> F::Output {
        (**self).call(args)
    }
}

impl<A, F: ?Sized> FnMut<A> for &F
where
    F: Fn<A>,
{
    #[rr::default_spec]
    #[rr::only_spec]
    fn call_mut(&mut self, args: A) -> F::Output {
        (**self).call(args)
    }
}

#[rr::instantiate("Params" := "{F::Params}")]
#[rr::instantiate("Pre" := "{F::Pre}")]
#[rr::instantiate("Post" := "{F::Post}")]
#[rr::instantiate("PostMut" := "λ π p s args s2 ret, (⌜s2 = s⌝ ∗ {F::Post} π p s args ret)%I")]
impl<A, F: ?Sized> FnOnce<A> for &F
where
    F: Fn<A>,
{
    type Output = F::Output;

    #[rr::default_spec]
    #[rr::only_spec]
    fn call_once(self, args: A) -> F::Output {
        (*self).call(args)
    }
}

impl<A, F: ?Sized> FnMut<A> for &mut F
where
    F: FnMut<A>,
{
    #[rr::default_spec]
    #[rr::only_spec]
    fn call_mut(&mut self, args: A) -> F::Output {
        (*self).call_mut(args)
    }
}

#[rr::instantiate("Params" := "{F::Params}")]
#[rr::instantiate("Pre" := "λ π p s args, {F::Pre} π p s.cur args")]
#[rr::instantiate("Post" := "λ π p s args ret, (∃ s2, {F::PostMut} π p s.cur args s2 ret ∗ gvar_pobs s.ghost ($# s2))%I")]
#[rr::instantiate("PostMut" := "λ π p s args s2 ret, ({F::PostMut} π p s.cur args s2.cur ret ∗ ⌜s.ghost = s2.ghost⌝)%I")]
impl<A, F: ?Sized> FnOnce<A> for &mut F
where
    F: FnMut<A>,
{
    type Output = F::Output;

    #[rr::default_spec]
    #[rr::only_spec]
    fn call_once(self, args: A) -> F::Output {
        (*self).call_mut(args)
    }
}
