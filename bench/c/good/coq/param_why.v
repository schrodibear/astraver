(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export param_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (mutable_x: Z),
  forall (HW_1: mutable_x = (x + y)),
  mutable_x = (x + y).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

