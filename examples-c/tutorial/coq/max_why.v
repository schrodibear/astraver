(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export max_spec_why.

(* Why obligation from file "why/max.why", characters 45-242 *)
Lemma max_impl_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (result: Z),
  forall (Post1: x > y /\ result = x \/ x <= y /\ result = y),
  (result >= x /\ result >= y) /\
  (forall (z:Z), (z >= x /\ z >= y -> z >= result)).
Proof.
intuition.
Save.

