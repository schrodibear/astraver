
Require Import Why.
Require Import Omega.

(* Why obligation from file "loop0.mlw", characters 316-327 *)
Lemma p_po_1 : 
  forall (x: Z),
  forall (Pre4: x >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (Pre3: Variant1 = x0),
  forall (Pre2: 0 <= x0 /\ x0 <= x),
  forall (Test2: x0 > 0),
  forall (x1: Z),
  forall (Post2: x1 = (x0 - 1)),
  (0 <= x1 /\ x1 <= x) /\ (Zwf 0 x1 x0).
 Proof.
 intuition.
 Qed.

(* Why obligation from file "loop0.mlw", characters 248-335 *)
Lemma p_po_2 : 
  forall (x: Z),
  forall (Pre4: x >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (Pre3: Variant1 = x0),
  forall (Pre2: 0 <= x0 /\ x0 <= x),
  forall (Test1: x0 <= 0),
  x0 = 0.
Proof.
intuition.
Qed.

(* Why obligation from file "loop0.mlw", characters 281-297 *)
Lemma p_po_3 : 
  forall (x: Z),
  forall (Pre4: x >= 0),
  0 <= x /\ x <= x.
Proof.
intuition.
Qed.
