(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export dowhile_spec_why.

(* Why obligation from file "why/dowhile.why", line 0, characters 0-0: *)
(*Why goal*) Lemma main_impl_po_1 : 
  forall (x: Z),
  forall (HW_1: (* File \"dowhile.c819618234.c1069824147.i\", line 0, characters 10-16 *)
                x >= 0),
  forall (x0: Z),
  forall (HW_2: x0 = 0),
  forall (i: Z),
  forall (HW_3: i = 10),
  (* File \"dowhile.c819618234.c1069824147.i\", line 0, characters 11-37 *)
  (x0 = (10 - i) /\ 10 >= i /\ i > 0).
Proof.
intuition.
Save.

(* Why obligation from file "why/dowhile.why", line 0, characters 0-0: *)
(*Why goal*) Lemma main_impl_po_2 : 
  forall (x: Z),
  forall (HW_1: (* File \"dowhile.c819618234.c1069824147.i\", line 0, characters 10-16 *)
                x >= 0),
  forall (x0: Z),
  forall (HW_2: x0 = 0),
  forall (i: Z),
  forall (HW_3: i = 10),
  forall (i0: Z),
  forall (x1: Z),
  forall (HW_4: (* File \"dowhile.c819618234.c1069824147.i\", line 0, characters 11-37 *)
                (x1 = (10 - i0) /\ 10 >= i0 /\ i0 > 0)),
  forall (x2: Z),
  forall (HW_5: x2 = (x1 + 1)),
  forall (i1: Z),
  forall (HW_6: i1 = (i0 - 1)),
  forall (HW_7: i1 > 0),
  (* File \"dowhile.c819618234.c1069824147.i\", line 0, characters 11-37 *)
  (x2 = (10 - i1) /\ 10 >= i1 /\ i1 > 0) /\ (Zwf 0 i1 i0).
Proof.
intuition.
Save.

(* Why obligation from file "why/dowhile.why", line 0, characters 0-0: *)
(*Why goal*) Lemma main_impl_po_3 : 
  forall (x: Z),
  forall (HW_1: (* File \"dowhile.c819618234.c1069824147.i\", line 0, characters 10-16 *)
                x >= 0),
  forall (x0: Z),
  forall (HW_2: x0 = 0),
  forall (i: Z),
  forall (HW_3: i = 10),
  forall (i0: Z),
  forall (x1: Z),
  forall (HW_4: (* File \"dowhile.c819618234.c1069824147.i\", line 0, characters 11-37 *)
                (x1 = (10 - i0) /\ 10 >= i0 /\ i0 > 0)),
  forall (x2: Z),
  forall (HW_5: x2 = (x1 + 1)),
  forall (i1: Z),
  forall (HW_6: i1 = (i0 - 1)),
  forall (HW_8: i1 <= 0),
  (* File \"dowhile.c819618234.c1069824147.i\", line 0, characters 25-32 *)
  x2 = 10.
Proof.
intuition.
discriminate.
Save.

Proof.
intuition.
Save.

