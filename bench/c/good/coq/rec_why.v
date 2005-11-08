(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export rec_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (x: Z),
  forall (HW_1: (* File \"rec.c\", line 4, characters 14-20:\n *) x >= 0),
  forall (HW_2: x = 0),
  (* File \"rec.c\", line 4, characters 62-74:\n *) 0 = 0.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (x: Z),
  forall (HW_1: (* File \"rec.c\", line 4, characters 14-20:\n *) x >= 0),
  forall (HW_3: x <> 0),
  (* File \"rec.c\", line 4, characters 14-20:\n *) (x - 1) >= 0.
Proof.
intuition.
Save.

