(* Load Programs. *)(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.


(* Why obligation from file "good-c/call.c", characters 113-116 *)
Lemma f_po_1 : 
  forall (y: Z),
  forall (ddd: Z),
  forall (z: Z),
  forall (Pre1: y = ddd),
  forall (u: Z),
  forall (Post3: u = z),
  forall (c_aux_1: Z),
  forall (Post2: c_aux_1 = u),
  forall (u1: Z),
  forall (Post1: u1 = (u + 1)),
  c_aux_1 = z.
Proof.
intuition.
Qed.


(* Why obligation from file "good-c/call.c", characters 174-177 *)
Lemma main_po_1 : 
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (x1: Z),
  forall (Post2: x1 = (x0 + 1)),
  (forall (result:Z), (result = 2 -> result = 2)) /\ 1 = x1.
Proof.
intuition.
Qed.


