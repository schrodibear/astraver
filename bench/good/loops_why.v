
Require Import Why.
Require Import Omega.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma loop1_po_1 : 
  forall (i: Z),
  forall (HW_2: i <= 10),
  forall (i0: Z),
  forall (HW_3: i0 <= 10),
  forall (HW_4: i0 < 10),
  forall (i1: Z),
  forall (HW_5: i1 = (i0 + 1)),
  i1 <= 10 /\ (Zwf 0 (10 - i1) (10 - i0)).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma loop1_po_2 : 
  forall (i: Z),
  forall (HW_2: i <= 10),
  forall (i0: Z),
  forall (HW_3: i0 <= 10),
  forall (HW_6: i0 >= 10),
  i0 = 10.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma oppose_po_1 : 
  forall (x: Z),
  forall (x0: Z),
  forall (HW_1: x0 = (Zopp x)),
  x0 = (Zopp x).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma loop2_po_1 : 
  forall (x: Z),
  forall (HW_2: x <= 10),
  forall (x0: Z),
  forall (HW_3: x0 <= 10),
  forall (HW_4: x0 < 10),
  forall (x1: Z),
  forall (HW_5: x1 = (x0 + 1)),
  x1 <= 10 /\ (Zwf 0 (10 - x1) (10 - x0)).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma loop2_po_2 : 
  forall (x: Z),
  forall (HW_2: x <= 10),
  forall (x0: Z),
  forall (HW_3: x0 <= 10),
  forall (HW_6: x0 >= 10),
  x0 = 10.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma loop2_po_3 : 
  forall (x: Z),
  forall (HW_2: x <= 10),
  forall (x0: Z),
  forall (HW_3: x0 <= 10),
  forall (HW_6: x0 >= 10),
  forall (HW_7: x0 > 0),
  forall (x1: Z),
  forall (HW_8: x1 = (Zopp x0)),
  x1 = (Zopp 10).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma loop2_po_4 : 
  forall (x: Z),
  forall (HW_2: x <= 10),
  forall (x0: Z),
  forall (HW_3: x0 <= 10),
  forall (HW_6: x0 >= 10),
  forall (HW_9: x0 <= 0),
  x0 = (Zopp 10).
Proof.
intuition.
Save.

