#![allow(unused)]

/// Using closure arguments
#[rr::verify]
// NOTE: the params needs to be put into the trait_incl assumption!
//#[rr::params("c" : "Z")]
// For the general form, we don't have syntactic sugar.
#[rr::requires(#trait T::Pre := "λ _ _ _ _, True%I")]
#[rr::requires(#trait T::Post := "λ _ _ _ _ ret, (∃ c : Z, ⌜ret = c⌝)%I")]
#[rr::requires(#trait T::PostMut := "λ _ _ _ _ _ _, True%I")]
#[rr::requires(#trait T::Params := "unit")]
//#[rr::require(#closure "T" : "True" -> "∃ c : Z, ret = c")]
//#[rr::closure_computes("T", "λ _, c")]
//#[rr::params("f" : "() → Z")]
//#[rr::require(#assume "{T::Post}": "ret = #(f args_0)")]
//#[rr::require("∃ c, ∀ x, f x = c")]
// TODO: this should make the spec non-trivial
//#[rr::requires(#iris "{T::Pre} ($# x) ()")]
fn closure_test_arg_fnonce_1<T>(x: T)
    where T: FnOnce() -> i32
{
    let _ = x();
}

#[rr::verify]
#[rr::requires(#trait T::Pre := "λ _ _ _ x, ⌜x = -[42]⌝%I")]
// TODO: allow to omit post
#[rr::requires(#trait T::Post := "λ _ _ _ _ ret, True%I")]
#[rr::requires(#trait T::PostMut := "λ _ _ _ _ _ _, True%I")]
#[rr::requires(#trait T::Params := "unit")]
fn closure_test_arg_fnonce_2<T>(x: T)
    where T: FnOnce(i32) -> i32
{
    let r = x(42);
}

// Problem: this will assume by default that the spec is trivial, right?
// Point: I want the pre to remain trivial, but accept an arbitrary post.
// I cannot really specify that well, currently.
#[rr::verify]
#[rr::requires(#trait T::Pre := "λ _ _ _ _, True%I")]
#[rr::requires(#trait T::Post := "λ _ _ _ _ ret, True%I")]
#[rr::requires(#trait T::PostMut := "λ _ _ _ _ _ _, True%I")]
#[rr::requires(#trait T::Params := "unit")]
// TODO: allow this
//#[rr::params("P")]
//#[rr::requires(#trait T::Pre := "λ _ _, True%I")]
//#[rr::requires(#trait T::Post := "P")]
// TODO: allow this
//#[rr::exists("r")]
//#[rr::ensures(#iris "{T::Post} x () r")]
fn closure_test_arg_fnonce_3<T, W>(x: T)
    where T: FnOnce() -> W
{
    let _ = x();
}

#[rr::verify]
#[rr::requires(#trait T::Pre := "λ _ _ _ _, True%I")]
#[rr::requires(#trait T::Post := "λ _ _ _ _ ret, True%I")]
#[rr::requires(#trait T::PostMut := "λ _ _ _ _ _ _, True%I")]
#[rr::requires(#trait T::Params := "unit")]
fn closure_test_arg_fn_1<T>(x: T)
    where T: Fn()
{
    x()
}
// Note: Do I ever want to require how the state changes?
// I guess not, because I don't even know what the state is.
// I mean, I could require that there exists some projection, etc.. but that does not seem worth it.

#[rr::verify]
#[rr::requires(#trait T::Pre := "λ _ _ _ _, True%I")]
#[rr::requires(#trait T::Post := "λ _ _ _ _ ret, True%I")]
#[rr::requires(#trait T::PostMut := "λ _ _ _ _ _ _, True%I")]
#[rr::requires(#trait T::Params := "unit")]
fn closure_test_arg_fn_2<T>(x: T)
    where T: Fn() -> i32
{
    x();
}

#[rr::verify]
#[rr::requires(#trait T::Pre := "λ _ _ _ _, True%I")]
#[rr::requires(#trait T::Post := "λ _ _ _ _ ret, True%I")]
#[rr::requires(#trait T::PostMut := "λ _ _ _ _ _ _, True%I")]
#[rr::requires(#trait T::Params := "unit")]
fn closure_test_arg_fnmut_1<T>(mut x: T)
    where T: FnMut()
{
    x()
}

// Calling functions with closures
#[rr::verify]
#[rr::requires(#trait T::Pre := "λ _ _ _ _, True%I")]
#[rr::requires(#trait T::Post := "λ _ _ _ _ ret, True%I")]
#[rr::requires(#trait T::PostMut := "λ _ _ _ _ _ _, True%I")]
#[rr::requires(#trait T::Params := "unit")]
fn closure_test_call_fnonce_0<T>(x: T)
    where T: FnOnce() -> i32
{
    closure_test_arg_fnonce_1(x);
}

#[rr::verify]
fn closure_test_call_fnonce_1_0<T>(x: T) {
    let clos =
        #[rr::verify]
        || { x; 42 };
    closure_test_arg_fnonce_1(clos);
}


#[rr::verify]
fn closure_test_call_fnonce_3_0<T>(x: T) {
    let clos =
        #[rr::verify]
        || { x; 42 };
    closure_test_arg_fnonce_3(clos);
}

#[rr::verify]
fn closure_test_call_fnonce_3_1<T, W>(x: T, y: W) {
    let clos =
        #[rr::verify]
        || { x; y };
    closure_test_arg_fnonce_3(clos);
}

#[rr::verify]
fn closure_test_call_fnonce_1_1<T>(x: T) {
    // Point: we're doing a shared capture of y
    let y = 42;
    let clos =
        #[rr::verify]
        || { x; y };
    closure_test_arg_fnonce_1(clos);
}

#[rr::verify]
fn closure_test_call_fnonce_1() {
    let a =
        #[rr::verify] || { 42 };
    closure_test_arg_fnonce_1(a);
}

#[rr::verify]
fn closure_test_call_fnonce_2() {
    closure_test_arg_fnonce_2(#[rr::verify]
        |x| { if x < 10 { x + 2 } else { x }  });
}

#[rr::verify]
fn closure_test_call_fnonce_2_2() {
    let clos = #[rr::verify]
        #[rr::requires("x < 50")]
        |x: i32| { x + 2 };
    closure_test_arg_fnonce_2(clos);
}

// TODO
#[rr::skip]
#[rr::verify]
fn closure_test_call_fnmut_1_0() {
    let mut y = 2;
    let clos =
        #[rr::verify]
        #[rr::ensures("{y.*new} = 1")]
        || { y = 1; 42 };

    closure_test_arg_fnonce_3(clos);

    // Point: I want to pass down all the observations.
    // But that is hard to specify and thread through automatically.
    // And I don't even know that the function I'm calling will actually call the closure!
    assert!(y == 1);
}

// TODO
#[rr::skip]
#[rr::verify]
fn closure_test_call_fn_2_0() {
    let mut y = 2;
    let clos =
        #[rr::verify]
        // TODO: this should be statically dispatched. It should be an invariant of the closure
        // that the callee of the closure does not need to worry about.
        #[rr::requires("{y} < 10")]
        #[rr::returns("({y} + 42)%Z")]
        || { y + 42 };

    closure_test_arg_fn_2(clos);

    // Point: I want to pass down all the observations.
    // But that is hard to specify and thread through automatically.
    // And I don't even know that the function I'm calling will actually call the closure!
    assert!(y == 1);
}


// TODO
#[rr::skip]
#[rr::verify]
fn closure_test_call_fnmut_1() {
    let mut x = 1;
    closure_test_arg_fnmut_1(
        #[rr::verify]
        #[rr::requires("{x} < 10")]
        #[rr::ensures("{x.*new} = {x} + 2")]
        || { x += 2; });
}

#[rr::verify]
fn closure_test_call_fn_1() {
    closure_test_arg_fn_1(#[rr::verify] || { });
}


/// Closures with no captures
#[rr::returns("()")]
fn closure_test1() {

    // Fn-closure
    let x =
        #[rr::requires("(2 * x)%Z ∈ i32")]
        #[rr::returns("(2 * x)%Z")]
        |x: i32| {
            x * 2
        };

    // here we call the closure's implementation
    let y = x(2);
    assert!(y == 4);
}

// TODO: propagate assumptions to contained closures
#[rr::skip]
#[rr::requires(#trait T::Pre := "λ _ _ _ _, True%I")]
#[rr::requires(#trait T::Post := "λ _ _ _ _ ret, True%I")]
#[rr::requires(#trait T::PostMut := "λ _ _ _ _ _ _, True%I")]
fn closure_test8<T, U>(x: T, y: U)
    where U: FnOnce(T)
{
    let cls =
        #[rr::skip]
        |a: T, w: U| { w(a) };

    cls(x, y);
}

#[rr::returns("()")]
fn closure_test12() {

    // Fn-closure
    let x =
        #[rr::requires("(y * x)%Z ∈ i32")]
        #[rr::returns("(y * x)%Z")]
        |x: i32, y: i32| {
            x * y
        };

    // here we call the closure's implementation
    assert!(x(2, 2) == 4);
}

#[rr::verify]
fn closure_test6<T>(x: T) {
    let cls =
        #[rr::returns("a")]
        |a: T| { a };

    cls(x);
}

/// Closures with shared captures
#[rr::returns("()")]
fn closure_test5() {
    let x = 5;

    // Fn-closure with a shared capture
    let x =
        #[rr::requires("(2 * {x})%Z ∈ i32")]
        #[rr::returns("(2 * {x})%Z")]
        || {
            x * 2
        };

    // here we call the closure's implementation
    assert!(x() == 10);
}

// TODO: we're having some weird anomaly with the mul method in the closure here.
// Somehow the impl lifetime parameter is duplicated to a late-bound of the method itself.
#[rr::skip]
#[rr::requires("z < 10")]
fn closure_test9(z: &u32) {
    let x = 5;

    // Fn-closure
    let x =
        #[rr::skip]
        #[rr::requires("({*z} * {x})%Z ∈ u32")]
        #[rr::returns("({*z} * {x})%Z")]
        || {
            x * z
        };

    // here we call the closure's implementation
    assert!(x() == z * 5);
}

/// Closures with mutable captures
#[rr::returns("()")]
fn closure_test2() {
    let mut y = 2;

    // here, we prove initialization of the closure

    let mut x =
        // Note: the closure code has a doubly-nested mutable references, since it gets a mutref to
        // the capture also.
        #[rr::requires("(2 * {y}) ∈ i32")]
        #[rr::ensures("{y.*new} = 2 * {y}")]
        || { y *= 2; };

    x();
    x();

    // here, we deinitialize the closure
    assert!(y == 8);
}

#[rr::requires("(4* y.cur) ∈ i32")]
#[rr::observe("y.ghost" : "y.cur * 4")]
#[rr::tactics("unsafe_unfold_common_caesium_defs; solve_goal.")]
fn closure_test3(y: &mut i32) {
    let mut z = 5;
    let mut yy = 423;

    let mut x =
        // this effectively takes a mutable reference for initialization
        // TODO: we should specify the projection here.
        #[rr::requires("(2 * {*y}) ∈ i32")]
        #[rr::requires("(5 * {z}) ∈ i32")]
        #[rr::ensures("{(*y).*new} = 2 * {*y}")]
        #[rr::ensures("{z.*new} = 5 * {z}")]
        || { *y *= 2; z *= 5; };

    x();
    x();

    assert!(z == 5*5*5);
}

// TODO: propagate assumptions to contained closures
//#[rr::verify]
#[rr::skip]
#[rr::requires(#trait T::Pre := "λ _ _ _ _, True%I")]
#[rr::requires(#trait T::Post := "λ _ _ _ _ ret, True%I")]
#[rr::requires(#trait T::PostMut := "λ _ _ _ _ _ _, True%I")]
#[rr::requires(#trait T::Params := "unit")]
fn closure_test7<T, U>(x: T, y: U)
    where U: FnOnce(T)
{
    let cls =
        #[rr::skip]
        |a: T| { y(a) };

    cls(x);
}


// This test demonstrates the case where even the arguments of a closure may use external
// lifetimes, in lieu of early bounds.
#[rr::verify]
fn closure_test10_helper<'a, T>(x: T, v: &'a i32) 
    where T: FnMut(&'a i32)
{

}
#[rr::verify]
fn closure_test10() {
    let a = 4;
    let b : i32 = 5;
    let ar = &a;
    closure_test10_helper(
        #[rr::requires("(y + 2) ∈ i32")]
        |y: &i32| {
            b;
            *y + 2;
        }, ar);
}

// HRTB
#[rr::verify]
#[rr::requires(#trait T::Pre := "λ _ _ _ _, True%I")]
#[rr::requires(#trait T::Post := "λ _ _ _ _ ret, True%I")]
#[rr::requires(#trait T::PostMut := "λ _ _ _ _ _ _, True%I")]
#[rr::requires(#trait T::Params := "unit")]
fn closure_test_call_hrtb_1<T>(x: T)
    where T: for<'a> Fn(&'a i32) -> i32
{
    let a = 2;
    x(&a);
}
#[rr::verify]
fn closure_test_hrtb_1() {
    let x =
        #[rr::returns("y")]
        |y: &i32| {
            *y
        };

    let a = 4;
    let b = 6;

    closure_test_call_hrtb_1(x);
}

#[rr::verify]
fn closure_test_hrtb_2() {
    let x =
        #[rr::requires("(y + 2) ∈ i32")]
        #[rr::returns("y + 2")]
        |y: &i32| {
            *y + 2
        };

    let a = 4;
    let b = 6;

    assert!(x(&a) == 6);
    assert!(x(&b) == 8);
}

// Late bound 
#[rr::verify]
fn closure_test_late_bound() {
    let a = 42;
    let x = 
        #[rr::verify]
        |y: &i32| {
            a;
        };
}

#[rr::verify]
fn closure_test_late_bound2() {
    let a = 42;
    let b = 100;
    let x = 
        #[rr::verify]
        |y: &i32, z: &i32| {
            b;
            a;
        };
}

#[rr::verify]
fn closure_test_late_bound3(v: &i32) {
    let a = 42;
    let b = 100;
    let x = 
        #[rr::verify]
        |y: &i32, z: &i32| {
            b;
            a;
            *v;
        };
}

#[rr::verify]
fn closure_test_late_bound4(v: &i32, w: &i32) {
    let a = 42;
    let b = 100;
    let x = 
        #[rr::verify]
        |y: &i32, z: &i32| {
            b;
            a;
            *v;
            *w;
        };
}


#[rr::only_spec]
fn closure_test_late_bound5<'a, T: 'a>(v: &i32, w: &'a i32) {
    let a = 42;
    let b = 100;
    let x = 
        #[rr::skip]
        |y: &i32, z: &i32| {
            b;
            a;
            *v;
            *w;
        };
}


mod fncoercion {
    fn bla(b: bool) {
        let x = |x: i32| {x };
        // uses ClosureFnPointer coercion to coerce whichever closure we pick to an fn pointer
        // (because there are no captures)
        let z = if b { x } else { |x : i32| { x } };
        // then we use the closure instance for fn pointers
        blub(z);
    }

    fn blub<T>(mut x : T) where T: Fn(i32) -> i32 {
        x(43);
    }
}

// Note: probably I could try to have a more creusot-like language that compiles down to this
// representation

