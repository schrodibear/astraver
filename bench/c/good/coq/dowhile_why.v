(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/dowhile.why", characters 383-389 *)
Lemma main_impl_po_1 : 
  forall (x: Z),
  forall (Pre4: x >= 0),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (i0: Z),
  forall (Post2: i0 = 10),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (x1: Z),
  forall (Pre3: Variant1 = i1),
  forall (Pre2: x1 = (10 - i1) /\ 10 >= i1 /\ i1 > 0),
  forall (Test4: true = true),
  forall (x2: Z),
  forall (Post5: x2 = (x1 + 1)),
  forall (i2: Z),
  forall (Post6: i2 = (i1 - 1)),
  forall (Test3: i2 <= 0),
  (forall (result:unit), (result = tt -> x2 = 10)).
Proof.
intuition.
Save.

(* Why obligation from file "why/dowhile.why", characters 400-400 *)
Lemma main_impl_po_2 : 
  forall (x: Z),
  forall (Pre4: x >= 0),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (i0: Z),
  forall (Post2: i0 = 10),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (x1: Z),
  forall (Pre3: Variant1 = i1),
  forall (Pre2: x1 = (10 - i1) /\ 10 >= i1 /\ i1 > 0),
  forall (Test4: true = true),
  forall (x2: Z),
  forall (Post5: x2 = (x1 + 1)),
  forall (i2: Z),
  forall (Post6: i2 = (i1 - 1)),
  forall (Test2: i2 > 0),
  forall (result5: unit),
  forall (Post7: result5 = tt),
  (x2 = (10 - i2) /\ 10 >= i2 /\ i2 > 0) /\ (Zwf 0 i2 i1).
Proof.
intuition.
Save.

(* Why obligation from file "why/dowhile.why", characters 159-411 *)
Lemma main_impl_po_3 : 
  forall (x: Z),
  forall (Pre4: x >= 0),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (i0: Z),
  forall (Post2: i0 = 10),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (x1: Z),
  forall (Pre3: Variant1 = i1),
  forall (Pre2: x1 = (10 - i1) /\ 10 >= i1 /\ i1 > 0),
  forall (Test1: false = true),
  x1 = 10.
Proof.
intuition.
discriminate.
Save.

(* Why obligation from file "why/dowhile.why", characters 201-264 *)
Lemma main_impl_po_4 : 
  forall (x: Z),
  forall (Pre4: x >= 0),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (i0: Z),
  forall (Post2: i0 = 10),
  x0 = (10 - i0) /\ 10 >= i0 /\ i0 > 0.
Proof.
intuition.
Save.

