(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/clash.why", characters 96-119 *)
Lemma g_impl_po_1 : 
  forall (y: Z),
  forall (y_0_1: Z),
  forall (Post1: y_0_1 = 0),
  forall (result0: Z),
  forall (Post2: result0 = y_0_1),
  result0 = 0 /\ y = y.
Proof.
intuition.
Save.

