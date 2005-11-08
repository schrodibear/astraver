Require Import Why.
Require Import Omega.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma swap1_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (x0: Z),
  forall (HW_1: x0 = y),
  forall (y0: Z),
  forall (HW_2: y0 = x),
  x0 = y /\ y0 = x.
Proof.
intuition.
Qed.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma swap2_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (x0: Z),
  forall (HW_1: x0 = y),
  forall (y0: Z),
  forall (HW_2: y0 = x),
  x0 = y /\ y0 = x.
Proof.
intuition.
Qed.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma swap3_po_1 : 
  forall (a: Z),
  forall (b: Z),
  forall (a0: Z),
  forall (HW_1: a0 = b),
  forall (b0: Z),
  forall (HW_2: b0 = a),
  a0 = b /\ b0 = a.
Proof.
intuition.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma call_swap3_y_x_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (y0: Z),
  forall (x0: Z),
  forall (HW_1: y0 = x /\ x0 = y),
  x0 = y /\ y0 = x.
 (* call_swap3_y_x_po_1 *)
Proof.
intuition.
Qed.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma swap4_po_1 : 
  forall (a: Z),
  forall (b: Z),
  forall (tmp: Z),
  forall (HW_1: tmp = a),
  forall (a0: Z),
  forall (HW_2: a0 = b),
  forall (b0: Z),
  forall (HW_3: b0 = tmp),
  a0 = b /\ b0 = a.
Proof.
intuition.
Qed.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma call_swap4_x_y_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x = 3),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_2: x0 = y /\ y0 = x),
  y0 = 3.
Proof.
intuition.
Qed.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma call_swap4_y_x_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x = 3),
  forall (y0: Z),
  forall (x0: Z),
  forall (HW_2: y0 = x /\ x0 = y),
  y0 = 3.
Proof.
intuition.
Qed.


