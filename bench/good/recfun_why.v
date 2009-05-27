(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.

(* Why obligation from file "recfun.mlw", line 7, characters 29-37: *)
(*Why goal*) Lemma f1_po_1 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_2: x > 0),
  (Zwf 0 (x - 1) x).
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 7, characters 29-37: *)
(*Why goal*) Lemma f1_po_2 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_2: x > 0),
  forall (HW_3: (Zwf 0 (x - 1) x)),
  (x - 1) >= 0.
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 7, characters 49-59: *)
(*Why goal*) Lemma f1_po_3 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_6: x <= 0),
  x = 0.
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 14, characters 49-56: *)
(*Why goal*) Lemma f2_po_1 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_2: x > 0),
  forall (x0: Z),
  forall (HW_3: x0 = (x - 1)),
  (Zwf 0 x0 x).
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 14, characters 49-56: *)
(*Why goal*) Lemma f2_po_2 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_2: x > 0),
  forall (x0: Z),
  forall (HW_3: x0 = (x - 1)),
  forall (HW_4: (Zwf 0 x0 x)),
  x0 >= 0.
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 14, characters 65-70: *)
(*Why goal*) Lemma f2_po_3 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_7: x <= 0),
  x = 0.
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 19, characters 48-56: *)
(*Why goal*) Lemma f3_po_1 : 
  forall (a: Z),
  forall (x: Z),
  forall (HW_1: a >= 0),
  forall (HW_2: a > 0),
  forall (x0: Z),
  forall (HW_3: x0 = (x + 1)),
  (Zwf 0 (a - 1) a).
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 19, characters 48-56: *)
(*Why goal*) Lemma f3_po_2 : 
  forall (a: Z),
  forall (x: Z),
  forall (HW_1: a >= 0),
  forall (HW_2: a > 0),
  forall (x0: Z),
  forall (HW_3: x0 = (x + 1)),
  forall (HW_4: (Zwf 0 (a - 1) a)),
  (a - 1) >= 0.
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 19, characters 65-75: *)
(*Why goal*) Lemma f3_po_3 : 
  forall (a: Z),
  forall (x: Z),
  forall (HW_1: a >= 0),
  forall (HW_2: a > 0),
  forall (x0: Z),
  forall (HW_3: x0 = (x + 1)),
  forall (HW_4: (Zwf 0 (a - 1) a)),
  forall (HW_5: (a - 1) >= 0),
  forall (x1: Z),
  forall (HW_6: x1 = (x0 + (a - 1))),
  x1 = (x + a).
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 19, characters 65-75: *)
(*Why goal*) Lemma f3_po_4 : 
  forall (a: Z),
  forall (x: Z),
  forall (HW_1: a >= 0),
  forall (HW_7: a <= 0),
  x = (x + a).
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 25, characters 51-55: *)
(*Why goal*) Lemma f4_po_1 : 
  forall (a: Z),
  forall (x: Z),
  forall (HW_1: a >= 0),
  forall (HW_2: a > 0),
  forall (x0: Z),
  forall (HW_3: x0 = (x + 1)),
  forall (a0: Z),
  forall (HW_4: a0 = (a - 1)),
  (Zwf 0 a0 a).
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 25, characters 51-55: *)
(*Why goal*) Lemma f4_po_2 : 
  forall (a: Z),
  forall (x: Z),
  forall (HW_1: a >= 0),
  forall (HW_2: a > 0),
  forall (x0: Z),
  forall (HW_3: x0 = (x + 1)),
  forall (a0: Z),
  forall (HW_4: a0 = (a - 1)),
  forall (HW_5: (Zwf 0 a0 a)),
  a0 >= 0.
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 26, characters 4-15: *)
(*Why goal*) Lemma f4_po_3 : 
  forall (a: Z),
  forall (x: Z),
  forall (HW_1: a >= 0),
  forall (HW_2: a > 0),
  forall (x0: Z),
  forall (HW_3: x0 = (x + 1)),
  forall (a0: Z),
  forall (HW_4: a0 = (a - 1)),
  forall (HW_5: (Zwf 0 a0 a)),
  forall (HW_6: a0 >= 0),
  forall (x1: Z),
  forall (HW_7: x1 = (x0 + a0)),
  x1 = (x + a).
Proof.
intuition.
Save.

(* Why obligation from file "recfun.mlw", line 26, characters 4-15: *)
(*Why goal*) Lemma f4_po_4 : 
  forall (a: Z),
  forall (x: Z),
  forall (HW_1: a >= 0),
  forall (HW_8: a <= 0),
  x = (x + a).
Proof.
intuition.
Save.

