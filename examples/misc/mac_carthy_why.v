(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.

Definition max (x y:Z) : Z :=
  match Z_le_gt_dec x y with
  | left _ => y
  | right _ => x
  end.

(* Why obligation from file "mac_carthy.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma f91_po_1 : 
  forall (n: Z),
  forall (HW_1: n <= 100),
  forall (result: Z),
  forall (HW_2: (n + 11) <= 100 /\ result = 91 \/ (n + 11) >= 101 /\ result =
                (n + 11 - 10)),
  forall (result0: Z),
  forall (HW_3: result <= 100 /\ result0 = 91 \/ result >= 101 /\ result0 =
                (result - 10)),
  n <= 100 /\ result0 = 91 \/ n >= 101 /\ result0 = (n - 10).
Proof.
intuition.
Qed.

(* Why obligation from file "mac_carthy.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma f91_po_2 : 
  forall (n: Z),
  forall (HW_1: n <= 100),
  forall (result: Z),
  forall (HW_2: (n + 11) <= 100 /\ result = 91 \/ (n + 11) >= 101 /\ result =
                (n + 11 - 10)),
  (Zwf 0 (max 0 (101 - result)) (max 0 (101 - n))).
Proof.
intros n.
unfold Zwf, max. 
case (Z_le_gt_dec 0 (101 - n)); intuition.
subst result.
ring (101-91).
case (Z_le_gt_dec 0 10); intuition.
subst result.
case (Z_le_gt_dec 0 (101 - (n + 11 - 10))); intuition; omega.
Save.

(* Why obligation from file "mac_carthy.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma f91_po_3 : 
  forall (n: Z),
  forall (HW_1: n <= 100),
  (Zwf 0 (max 0 (101 - (n + 11))) (max 0 (101 - n))).
Proof.
unfold Zwf, max; intuition.
case (Z_le_gt_dec 0 (101 - n)); intuition.
case (Z_le_gt_dec 0 (101 - n)); intuition.
case (Z_le_gt_dec 0 (101 - (n+11))); intuition.
Save.

(* Why obligation from file "mac_carthy.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma f91_po_4 : 
  forall (n: Z),
  forall (HW_4: n > 100),
  n <= 100 /\ (n - 10) = 91 \/ n >= 101 /\ (n - 10) = (n - 10).
Proof.
intuition.
Save.

