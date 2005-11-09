(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Import Omega.

(*Why logic*) Definition q : Z -> Prop.
Admitted.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p1_po_1 : 
  forall (x: Z),
  forall (HW_1: (q (x + 1))),
  forall (x0: Z),
  forall (HW_2: x0 = (x + 1)),
  (q x0).
Proof.
intuition.
subst; trivial.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p2_po_1 : 
  forall (HW_1: (q 7)),
  forall (x: Z),
  forall (HW_2: x = (3 + 4)),
  (q x).
Proof.
intuition.
subst; trivial.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p3_po_1 : 
  forall (x: Z),
  forall (x0: Z),
  forall (HW_1: x0 = (x + 1)),
  forall (x1: Z),
  forall (HW_2: x1 = (x0 + 2)),
  x1 = (x + 3).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p4_po_1 : 
  forall (x: Z),
  forall (HW_1: x = 7),
  forall (x0: Z),
  forall (HW_2: x0 = (2 * x)),
  x0 = 14.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p5_po_1 : 
  (3 + 4) = 7.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p6_po_1 : 
  (3 + 4) = 7.
Proof.
intuition.
Save.



(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p7_po_1 : 
  (3 + (4 + 4)) = 11.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p8_po_1 : 
  forall (x: Z),
  forall (HW_1: (q (x + 1))),
  forall (x0: Z),
  forall (HW_2: x0 = (x + 1)),
  (q x0) /\ (3 + x0) = (x + 4).
Proof.
intuition.
subst; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p9_po_1 : 
  forall (x: Z),
  forall (HW_1: x = 1),
  forall (x0: Z),
  forall (HW_2: x0 = 2),
  (1 + 1) = 2 /\ x0 = 2.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p9a_po_1 : 
  forall (x: Z),
  forall (HW_1: x = 1),
  (1 + 1) = 2 /\ x = 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p10_po_1 : 
  forall (result: Z),
  forall (HW_1: result = (0 + 1)),
  result = 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p11_po_1 : 
  forall (result: Z),
  forall (HW_1: result = (0 + 1)),
  forall (result0: Z),
  forall (HW_2: result0 = (3 + 1)),
  (result + result0) = 5.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p11a_po_1 : 
  forall (result: Z),
  forall (HW_1: result = (1 + 1)),
  (result + result) = 4.
Proof.
intuition.
Save.



(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p12_po_1 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (x0: Z),
  forall (HW_2: x0 = (x + 1)),
  x0 = 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p13_po_1 : 
  forall (x: Z),
  forall (x0: Z),
  forall (HW_1: x0 = (x + 1)),
  forall (x1: Z),
  forall (HW_2: x1 = (x0 + 1)),
  x1 = (x + 2).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p13a_po_1 : 
  forall (x: Z),
  forall (x0: Z),
  forall (HW_1: x0 = (x + 1)),
  forall (x1: Z),
  forall (HW_2: x1 = (x0 + 1)),
  x1 = (x + 2).
Proof.
intuition.
Save.



(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p14_po_1 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (result: Z),
  forall (x0: Z),
  forall (HW_2: x0 = (x + 1) /\ result = x0),
  result = 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p15_po_1 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = 10),
  0 <= 0 /\ 0 < (array_length t).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p16_po_1 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = 10),
  0 <= 9 /\ 9 < (array_length t).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p17_po_1 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = 10 /\ 0 <= (access t 0) /\ (access t 0) <
                10),
  0 <= 0 /\ 0 < (array_length t).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p17_po_2 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = 10 /\ 0 <= (access t 0) /\ (access t 0) <
                10),
  forall (HW_2: 0 <= 0 /\ 0 < (array_length t)),
  forall (result: Z),
  forall (HW_3: result = (access t 0)),
  0 <= result /\ result < (array_length t).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p18_po_1 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = 10),
  forall (x: Z),
  forall (HW_2: x = 0),
  0 <= x /\ x < (array_length t).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p18_po_2 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = 10),
  forall (x: Z),
  forall (HW_2: x = 0),
  forall (HW_3: 0 <= x /\ x < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_4: t0 = (update t x x)),
  (access t0 0) = x.
Proof.
intuition.
subst; intuition.
(* FILL PROOF HERE *)
(* FILL PROOF HERE *)
Save.

