(* Load Programs. *)(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.

(* Why obligation from file "good-c/pointer.c", characters 72-78 *)
Lemma f_po_1 : 
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (c_aux_1: Z),
  forall (Post3: c_aux_1 = x0),
  forall (x1: Z),
  forall (Post2: x1 = (x0 + 1)),
  x1 = 1 /\ c_aux_1 = 0.
Proof.
intuition.
(* FILL PROOF HERE *)
Qed.



(* Why obligation from file "good-c/pointer.c", characters 187-196 *)
Lemma h_po_1 : 
  forall (z: Z),
  forall (Post2: z = 0),
  forall (z1: Z),
  forall (c_aux_2: Z),
  forall (Post4: z1 = 1 /\ c_aux_2 = 0),
  forall (c_aux_3: Z),
  forall (Post1: c_aux_3 = z1),
  (c_aux_2 + c_aux_3) = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Qed.


