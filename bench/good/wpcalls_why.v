(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.


(* Why obligation from file "good/wpcalls.mlw", characters 184-205 *)
(*Why goal*) Lemma p_po_1 : 
  forall (x: Z),
  forall (result: unit),
  forall (Post1: result = tt),
  forall (x0: Z),
  forall (Post5: x0 = (1 - x)),
  forall (x1: Z),
  forall (Post7: x1 = (1 - x0)),
  x1 = x.
Proof.
intuition.
Qed.


