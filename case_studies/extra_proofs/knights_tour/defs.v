From refinedrust Require Import typing.

(* !start spec(knights_tour.knights_tour) *)
Definition in_bounds (sz : nat) (p : Z * Z) :=
  name_hint "HlowerX" (0 ≤ p.1) ∧ name_hint "HupperX" (p.1 < sz) ∧ name_hint "HlowerY" (0 ≤ p.2) ∧ name_hint "HupperY" (p.2 < sz).
(* !end spec *)
