(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.


Proof.
intuition.
Qed.


Proof.
intuition.
Qed.


(* Why obligation from file "why/call.why", characters 175-183 *)
Lemma f_impl_po_1 : 
  forall (y: Z),
  forall (ddd: Z),
  forall (z: Z),
  forall (Pre1: y = ddd),
  forall (u: Z),
  forall (Post3: u = z),
  forall (caduceus: Z),
  forall (Post2: caduceus = u),
  forall (u1: Z),
  forall (Post1: u1 = (caduceus + 1)),
  caduceus = z.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/call.why", characters 357-359 *)
Lemma main_impl_po_1 : 
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (x1: Z),
  forall (Post2: x1 = (x0 + 1)),
  (forall (result:Z), (result = 2 -> result = 2)) /\ 1 = x1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

