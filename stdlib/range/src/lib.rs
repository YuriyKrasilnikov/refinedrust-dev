#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.range")]
#![rr::include("cmp")]
#![rr::include("option")]

#![feature(step_trait)]

#[rr::export_as(core::ops::Range)]
#[rr::refined_by("(rstart, rend)" : "{rt_of Idx} * {rt_of Idx}")]
pub struct Range<Idx> {
    /// The lower bound of the range (inclusive).
    #[rr::field("rstart")]
    pub start: Idx,
    /// The upper bound of the range (exclusive).
    #[rr::field("rend")]
    pub end: Idx,
}

#[rr::export_as(core::ops::Range)]
impl<Idx: PartialOrd<Idx>> Range<Idx> {
    // TODO: Spec doesn't work currently because spec language doesn't distinguish the two required
    // impls
    #[rr::skip]
    //#[rr::returns("bool_decide (({Idx::POrd} self.1 item = Some Less ∨ {Idx::POrd} self.1 item = Some Equal) ∧ {Idx::POrd} item self.2 = Some Less)")]
    pub fn contains<U>(&self, item: &U) -> bool
    where
        Idx: PartialOrd<U>,
        U: ?Sized + PartialOrd<Idx>,
    {
        unimplemented!();
        //<Self as RangeBounds<Idx>>::contains(self, item)
    }

    #[rr::returns("bool_decide (¬ {Idx::POrd} self.1 self.2 = Some Less)")]
    pub fn is_empty(&self) -> bool {
        !(self.start < self.end)
    }
}
