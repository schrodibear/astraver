(* Load Programs. *)(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.

(* Why obligation from file "good-c/rec.c", characters 115-123 *)
Lemma f_po_1 : 
  forall (x: Z),
  forall (Pre8: x >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = x0),
  forall (Pre6: x0 >= 0),
  forall (Test1: x0 <> 0),
  (x0 - 1) >= 0.
Proof.
intuition.
Qed.

(* Why obligation from file "good-c/rec.c", characters 46-144 *)
Lemma f_po_2 : 
  forall (x: Z),
  forall (Pre8: x >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = x0),
  forall (Pre6: x0 >= 0),
  forall (Test1: x0 <> 0),
  forall (Pre5: (x0 - 1) >= 0),
  forall (Pre3: (x0 - 1) >= 0),
  forall (Pre4: (x0 - 1) >= 0),
  (Zwf 0 (x0 - 1) Variant1).
Proof.
intuition.
Qed.


