(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.

(* Why obligation from file "", line 0, characters -1--1: *)
(*Why goal*) Lemma f_po_1 : 
  forall (b: Z),
  forall (b0: Z),
  forall (HW_1: b0 = (1 - b)),
  (b0 = b0 /\ b0 = (1 - b)).
Proof.
intuition.
Save.


(* Why obligation from file "", line 0, characters -1--1: *)
(*Why goal*) Lemma k_po_1 : 
  forall (b: Z),
  forall (HW_1: b = 0),
  forall (result: Z),
  forall (b0: Z),
  forall (HW_2: result = b0 /\ b0 = (1 - b)),
  forall (result0: Z),
  forall (b1: Z),
  forall (HW_3: result0 = b1 /\ b1 = (1 - b0)),
  forall (b1_0: Z),
  forall (HW_4: b1_0 = (1 - result + result0)),
  forall (result1: Z),
  forall (b2: Z),
  forall (HW_5: result1 = b2 /\ b2 = (1 - b1)),
  forall (result2: Z),
  forall (b3: Z),
  forall (HW_6: result2 = b3 /\ b3 = (1 - b2)),
  forall (b2_0: Z),
  forall (HW_7: b2_0 = (result1 * (1 - result2))),
  (b1_0 = 0 /\ b2_0 = 1).
Proof.
intuition; subst; trivial.
Save.


