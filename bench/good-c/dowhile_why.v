(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.


(* Why obligation from file "good-c/dowhile.c", characters 91-126 *)
Lemma main_po_1 : 
  forall (x: Z),
  forall (Pre4: x >= 0),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (i0: Z),
  forall (Post2: i0 = 10),
  forall (x1: Z),
  forall (Post3: x1 = (x0 + 1)),
  forall (i1: Z),
  forall (Post4: i1 = (i0 - 1)),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (x2: Z),
  forall (Pre3: Variant1 = i2),
  forall (Pre2: x2 = (10 - i2) /\ i2 >= 0),
  forall (Test2: i2 > 0),
  forall (x3: Z),
  forall (Post5: x3 = (x2 + 1)),
  forall (i3: Z),
  forall (Post6: i3 = (i2 - 1)),
  (x3 = (10 - i3) /\ i3 >= 0) /\ (Zwf 0 i3 i2).
Proof.
intuition.
Qed.

(* Why obligation from file "good-c/dowhile.c", characters 144-165 *)
Lemma main_po_2 : 
  forall (x: Z),
  forall (Pre4: x >= 0),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (i0: Z),
  forall (Post2: i0 = 10),
  forall (x1: Z),
  forall (Post3: x1 = (x0 + 1)),
  forall (i1: Z),
  forall (Post4: i1 = (i0 - 1)),
  x1 = (10 - i1) /\ i1 >= 0.
Proof.
intuition.
Qed.

(* Why obligation from file "good-c/dowhile.c", characters 54-211 *)
Lemma main_po_3 : 
  forall (x: Z),
  forall (Pre4: x >= 0),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (i0: Z),
  forall (Post2: i0 = 10),
  forall (x1: Z),
  forall (Post3: x1 = (x0 + 1)),
  forall (i1: Z),
  forall (Post4: i1 = (i0 - 1)),
  forall (i2: Z),
  forall (x2: Z),
  forall (Post7: (x2 = (10 - i2) /\ i2 >= 0) /\ i2 <= 0),
  x2 = 10.
Proof.
intuition.
Qed.



