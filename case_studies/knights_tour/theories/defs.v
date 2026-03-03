From refinedrust Require Import typing.

Definition in_bounds (sz : nat) (p : Z * Z) :=
  0 ≤ p.1 ∧ p.1 < sz ∧ 0 ≤ p.2 ∧ p.2 < sz.

(*
// fn in_bounds(self, p: Point) -> bool {
//     pearlite! {
//         0 <= p.x@ && p.x@< self.size@ && 0 <= p.y@ && p.y@ < self.size@
//     }
// }
 *)
