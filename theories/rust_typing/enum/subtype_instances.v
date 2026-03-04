From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import struct.def struct.subtype.
From refinedrust.enum Require Import def subtype subltype unfold.
From refinedrust Require Import programs.
From refinedrust Require Import options.


Section unfolding.
  Context `{!typeGS Σ}.

  (* For now, restrict to pretty conservative instances that only work if we can fold back to a type *)

  Lemma weak_subltype_enum_ofty_1 E L {rt rt2} (en : enum rt) variant {rte} (lte : ltype rte) re k r1 r2 (ty2 : type rt2) T :
    cast_ltype_to_type E L (EnumLtype en variant lte re) (λ ty1 ,
      weak_subltype E L k r1 r2 (◁ ty1) (◁ ty2) T)
    ⊢ weak_subltype E L k r1 r2 (EnumLtype en variant lte re) (◁ ty2) T.
  Proof.
    iIntros "(%ty1 & %Heqt & HT)".
    iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[] CTX HE HL") as "(#Hincl & HL & $)"; first done.
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; first apply Heqt.
    iFrame. iApply ltype_incl_trans; last done.
    iApply ltype_eq_ltype_incl_l.
    done.
  Qed.
  Definition weak_subltype_enum_ofty_1_inst := [instance @weak_subltype_enum_ofty_1].
  Global Existing Instance weak_subltype_enum_ofty_1_inst.

  Lemma mut_subltype_enum_ofty_1 E L {rt} (en : enum rt) variant {rte} (lte : ltype rte) re (ty2 : type rt) T :
    cast_ltype_to_type E L (EnumLtype en variant lte re) (λ ty1 ,
      mut_subltype E L (◁ ty1) (◁ ty2) T)
    ⊢ mut_subltype E L (EnumLtype en variant lte re) (◁ ty2) T.
  Proof.
    iIntros "(%ty1 & %Heqt & %Hsubt & $)".
    iPureIntro.
    etrans; last apply Hsubt.
    by apply full_eqltype_subltype_l.
  Qed.
  Definition mut_subltype_enum_ofty_1_inst := [instance @mut_subltype_enum_ofty_1].
  Global Existing Instance mut_subltype_enum_ofty_1_inst.

  Lemma mut_eqltype_enum_ofty_1 E L {rt} (en : enum rt) variant {rte} (lte : ltype rte) re (ty2 : type rt) T :
    cast_ltype_to_type E L (EnumLtype en variant lte re) (λ ty1 ,
      mut_eqltype E L (◁ ty1) (◁ ty2) T)
    ⊢ mut_eqltype E L (EnumLtype en variant lte re) (◁ ty2) T.
  Proof.
    iIntros "(%ty1 & %Heqt & %Hsubt & $)".
    iPureIntro.
    etrans; last apply Hsubt.
    done.
  Qed.
  Definition mut_eqltype_enum_ofty_1_inst := [instance @mut_eqltype_enum_ofty_1].
  Global Existing Instance mut_eqltype_enum_ofty_1_inst.
End unfolding.
