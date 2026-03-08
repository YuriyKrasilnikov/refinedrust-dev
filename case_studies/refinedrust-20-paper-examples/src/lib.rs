#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![allow(unused)]

#![rr::package("paper-examples-rr20")]
#![rr::include("stdlib")]

// Point: I want to be able to borrow the contents of the box, but not the box itself
// If I were to borrow the T field, would I be able to inject back? 
// 
// I'd have: 
// StructLtype [BlockedLtype T; ◁ List<T>] 
// Then I fold that to Coreable ?? 
//
// for Vec, I went to Coreable κ (Vec) I think. 
// in the process of folding, I'm updating the refinement.
//
// Here the same happens as well. 
// I'll need a stratification lemma that lifts coreable for enum. 
// Basically, these coreable lifting lemmas are what is needed to reborrow mutably below a type.
//
// I'll need two changes to make this work nicely:
// - allow invariants on enums, or (better) allow them on the constituent structs.
// - don't always require PlaceIn on the invariant struct fields. 
//
// Basically I need to be careful with the place_rfn placement to control where I can reborrow or not.
// 
//
// What if I allow invariants on structs here? 
// Maybe I can formulate the lemmas such that I _always_ use invariants (in order to avoid
// duplication)?
// 
//
//
//

#[rr::refined_by("list ({rt_of T})")]
//#[rr::refined_by("list (place_rfn {rt_of T})")]
enum List<T> {
    #[rr::pattern("nil")]
    Nil,
    #[rr::pattern("cons" $ "x", "xs")]
    //#[rr::refinement("-[x; xs]")]
    #[rr::refinement("(x, xs)")]
    #[rr::refined_by("(x, xs)" : "({rt_of T}) * (list ({rt_of T}))")]
    Cons(
        #[rr::field("x")]
        T, 
        #[rr::field("#xs")]
        Box<List<T>>),
}

impl<T> List<T> {
    #[rr::returns("[]")]
    fn empty() -> List<T> {
        Self::Nil
    }
}

#[rr::refined_by("l" : "list ({rt_of T})")]
struct ListIter<'a, T> {
    #[rr::field("#l")]
    l: &'a List<T>,    
}

#[rr::instantiate("Params" := "unit")]
#[rr::instantiate("Next" := "λ π _ l e l2, 
    (⌜if_None e (l = [] ∧ l2 = [])⌝∗
    ⌜if_Some e (λ e, l = e :: l2)⌝)%I")]
#[rr::instantiate("Inv" := "λ π _ s, True%I")]
impl<'a, T> Iterator for ListIter<'a, T> {
    type Item = &'a T;

    #[rr::default_spec]
    #[rr::trust_me]
    fn next(&mut self) -> Option<Self::Item> {
        match &self.l {
            List::Nil => None,
            List::Cons(a, b) => {
                self.l = b;
                Some(a)
            },
        }
    }
}


#[rr::instantiate("IntoIter" := "λ x, x")]
impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = ListIter<'a, T>;

    #[rr::default_spec]
    fn into_iter(self: &'a List<T>) -> Self::IntoIter {
        ListIter { l: self } 
    }
}


#[rr::returns("max_list_Z (min_int i32) v")]
fn max_list_i32(v: &List<i32>) -> i32 {
    let mut m = i32::MIN;

    for x in v {
        #[rr::inv_vars("m")]
        #[rr::inv("m = max_list_Z (min_int i32) {Hist}")]
        #[rr::ignore] ||{};

        m = m.max(*x);
    }

    m
}

#[rr::exists("MIN" : "{xt_of Self}")]
#[rr::exists("MIN_minimal" : "∀ x, {Self::Ord} {MIN} x ≠ Greater")]
trait Min : Ord {
    #[rr::returns("{MIN}")]
    fn minimum() -> Self;
}

#[rr::returns("max_list_cmp_def {T::Ord} {T::MIN} v")]
fn max_list<T>(v: &List<T>) -> T 
    where T: Ord + Min + Copy
{
    let mut m = T::minimum();

    for x in v {
        #[rr::inv_vars("m")]
        #[rr::inv("m = max_list_cmp_def {T::Ord} {T::MIN} {Hist}")]
        #[rr::ignore] ||{};

        m = m.max(*x);
    }

    m
}
