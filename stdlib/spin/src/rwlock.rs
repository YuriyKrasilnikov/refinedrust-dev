use std::ops::{Deref, DerefMut};
use crate::relax::*;
use core::marker::PhantomData;



#[rr::export_as(spin::rwlock::RwLock)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x", "y")]
pub struct RwLock<T : ?Sized, R = Spin> {
    #[rr::field("y")]
    phantom: PhantomData<R>,
    #[rr::field("x")]
    data: PhantomData<T>,
}

#[rr::export_as(spin::rwlock::RwLockReadGuard)]
#[rr::refined_by("x" : "{rt_of T}")]
pub struct RwLockReadGuard<'a, T: 'a + ?Sized> {
    #[rr::field("#x")]
    _t: &'a T,
}

#[rr::export_as(spin::rwlock::RwLockWriteGuard)]
#[rr::refined_by("x" : "place_rfn {rt_of T}")]
#[rr::exists("y")]
pub struct RwLockWriteGuard<'a, T: 'a + ?Sized, R = Spin> {
    #[rr::field("#tt")]
    _l: &'a RwLock<T>,
    #[rr::field("y")]
    _r: R,
}


#[rr::export_as(spin::rwlock::RwLock)]
#[rr::only_spec]
impl<T, R> RwLock<T, R> {

    #[rr::returns("()")]
    pub fn new(t: T) -> RwLock<T, R> {
        unimplemented!();
    }
}

#[rr::export_as(spin::rwlock::RwLock)]
#[rr::only_spec]
impl<T, R: RelaxStrategy> RwLock<T, R> {

    #[rr::verify]
    pub fn read(&self) -> RwLockReadGuard<'_, T> {
        unimplemented!();
    }

    #[rr::verify]
    pub fn write(&self) -> RwLockWriteGuard<'_, T, R> {
        unimplemented!();
    }
}


#[rr::instantiate("DerefInto" := "id")]
#[rr::only_spec]
impl<'rwlock, T: ?Sized, R> Deref for RwLockWriteGuard<'rwlock, T, R> {
    type Target = T;

    fn deref(&self) -> &T {
        // Safety: We know statically that only we are referencing data
        //unsafe { &*self.data }
        unimplemented!();
    }
}

#[rr::instantiate("DerefMutInject" := "λ old γ, 👻 γ")]
#[rr::only_spec]
impl<'rwlock, T: ?Sized, R> DerefMut for RwLockWriteGuard<'rwlock, T, R> {
    fn deref_mut(&mut self) -> &mut T {
        // Safety: We know statically that only we are referencing data
        //unsafe { &mut *self.data }
        unimplemented!();
    }
}
