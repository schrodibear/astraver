(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/rec.why", characters 74-132 *)
Lemma f_impl_po_1 : 
  forall (x: Z),
  forall (Pre3: x >= 0),
  (x <> 0 -> (x - 1) >= 0).
Proof.
intuition.
Save.

(* Why obligation from file "why/rec.why", characters 33-162 *)
Lemma f_impl_po_2 : 
  forall (x: Z),
  forall (Pre3: x >= 0),
  forall (Pre2: (x <> 0 -> (x - 1) >= 0)),
  forall (result: Z),
  forall (Post1: x = 0 /\ result = 0 \/ x <> 0 /\ result = 0),
  result = 0.
Proof.
intuition.
Save.

