(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/enum.why", characters 33-82 *)
Lemma f_impl_po_1 : 
  forall (result: unit),
  forall (Post1: result = tt),
  y = 4.
Proof.
rewrite enum_E_y; intuition.
Save.

