(* Load Programs. *)(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.

Definition max (x y:Z) : Z :=
  match Z_le_gt_dec x y with
  | left _ => y
  | right _ => x
  end.

(* Why obligation from file "mac_carthy.mlw", characters 122-254 *)
Lemma f91_po_1 : 
  forall (Variant1: Z),
  forall (n0: Z),
  forall (Pre2: Variant1 = (max 0 (101 - n0))),
  forall (Test2: n0 <= 100),
  (Zwf 0 (max 0 (101 - (n0 + 11))) Variant1).
Proof.
intros Variant1 n.
 unfold Zwf, max.
case (Z_le_gt_dec 0 (101 - n)); intros Pre2 Test2;
 case (Z_le_gt_dec 0 (101 - (n + 11))); intuition; omega.
Qed.

(* Why obligation from file "mac_carthy.mlw", characters 122-254 *)
Lemma f91_po_2 : 
  forall (Variant1: Z),
  forall (n0: Z),
  forall (Pre2: Variant1 = (max 0 (101 - n0))),
  forall (Test2: n0 <= 100),
  forall (aux_3: Z),
  forall (Post5: (n0 + 11) <= 100 /\ aux_3 = 91 \/ (n0 + 11) >= 101 /\
                 aux_3 = (n0 + 11 - 10)),
  (Zwf 0 (max 0 (101 - aux_3)) Variant1).
Proof.
intros Variant1 n.
 unfold Zwf, max.
case (Z_le_gt_dec 0 (101 - n)); intros H Pre2 Test2 aux_1 Post5;
 case (Z_le_gt_dec 0 (101 - aux_1)); intuition omega.
Qed.

(* Why obligation from file "mac_carthy.mlw", characters 149-169 *)
Lemma f91_po_3 : 
  forall (Variant1: Z),
  forall (n0: Z),
  forall (Pre2: Variant1 = (max 0 (101 - n0))),
  forall (Test2: n0 <= 100),
  forall (aux_3: Z),
  forall (Post5: (n0 + 11) <= 100 /\ aux_3 = 91 \/ (n0 + 11) >= 101 /\
                 aux_3 = (n0 + 11 - 10)),
  forall (result0: Z),
  forall (Post7: aux_3 <= 100 /\ result0 = 91 \/ aux_3 >= 101 /\ result0 =
                 (aux_3 - 10)),
  n0 <= 100 /\ result0 = 91 \/ n0 >= 101 /\ result0 = (n0 - 10).
Proof.
intuition omega.
Qed.

(* Why obligation from file "mac_carthy.mlw", characters 181-187 *)
Lemma f91_po_4 : 
  forall (Variant1: Z),
  forall (n0: Z),
  forall (Pre2: Variant1 = (max 0 (101 - n0))),
  forall (Test1: n0 > 100),
  n0 <= 100 /\ (n0 - 10) = 91 \/ n0 >= 101 /\ (n0 - 10) = (n0 - 10).
Proof.
intuition omega.
Qed.


