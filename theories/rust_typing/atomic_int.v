From refinedrust Require Export existentials_atomic.
From refinedrust Require Import int.
From refinedrust Require Import options.

(** Semantic type for Rust atomic integers (AtomicU8, AtomicI32, etc.).

    Uses [at_ex_plain_t] with an identity invariant: the logical refinement [r]
    equals the physical inner value [x]. Parameterized by [int_type], so one
    definition covers all 10 stable integer atomics (AtomicU8 through AtomicIsize).

    Sharing is handled automatically by [at_bor] (Iris concurrent invariant). *)

Section atomic_int.
  Context `{!typeGS Σ}.

  Definition atomic_int_inv : at_ex_inv_def ZRT ZRT :=
    at_mk_ex_inv_def
      (λ (_π : thread_id) (x : Z) (r : Z), ⌜x = r⌝)%I
      []
      [].

  Definition atomic_int_t (it : int_type) : type ZRT :=
    at_ex_plain_t ZRT ZRT atomic_int_inv (int it).

End atomic_int.
