(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/call.why", characters 142-188 *)
Lemma f_impl_po_1 : 
  forall (y: Z),
  forall (ddd: Z),
  forall (z: Z),
  forall (Pre1: y = ddd),
  forall (u: Z),
  forall (Post4: u = z),
  forall (caduceus: Z),
  forall (Post3: caduceus = u),
  forall (u1: Z),
  forall (Post1: u1 = (caduceus + 1)),
  forall (result0: Z),
  forall (Post2: result0 = caduceus),
  result0 = z.
Proof.
intuition.
Save.

(* Why obligation from file "why/call.why", characters 323-357 *)
Lemma main_impl_po_1 : 
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (x1: Z),
  forall (Post6: x1 = (x0 + 1)),
  forall (result1: Z),
  forall (Post7: result1 = x1),
  (forall (result:Z), (result = 2 -> result = 2)) /\ 1 = result1.
Proof.
intuition.
Save.

