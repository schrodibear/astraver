(* Load Programs. *)Require Import Why.
Require Import Omega.

(* Why obligation from file "swap0.mlw", characters 149-174 *)
Lemma swap1_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (t: Z),
  forall (Post3: t = x),
  forall (x0: Z),
  forall (Post1: x0 = y),
  forall (y0: Z),
  forall (Post2: y0 = t),
  x0 = y /\ y0 = x.
Proof.
intuition.
Qed.


(* Why obligation from file "swap0.mlw", characters 316-358 *)
Lemma swap2_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (t: Z),
  forall (Post3: t = x),
  forall (x0: Z),
  forall (Post1: x0 = y),
  forall (y0: Z),
  forall (Post2: y0 = t),
  x0 = y /\ y0 = x.
Proof.
intuition.
Qed.


(* Why obligation from file "swap0.mlw", characters 509-534 *)
Lemma swap3_po_1 : 
  forall (a: Z),
  forall (b: Z),
  forall (t: Z),
  forall (Post3: t = a),
  forall (a0: Z),
  forall (Post1: a0 = b),
  forall (b0: Z),
  forall (Post2: b0 = t),
  a0 = b /\ b0 = a.
Proof.
intuition.
Qed.


(* Why obligation from file "swap0.mlw", characters 654-678 *)
Lemma test_swap3_po_1 : 
  forall (c: Z),
  forall (Post2: c = 1),
  forall (d: Z),
  forall (Post1: d = 2),
  forall (c1: Z),
  forall (d1: Z),
  forall (Post4: c1 = d /\ d1 = c),
  d1 = 1.
 (* test_swap3_po_1 *)
Proof.
intuition.
Qed.



(* Why obligation from file "swap0.mlw", characters 790-826 *)
Lemma call_swap3_y_x_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (y0: Z),
  forall (x0: Z),
  forall (Post1: y0 = x /\ x0 = y),
  x0 = y /\ y0 = x.
 (* call_swap3_y_x_po_1 *)
Proof.
intuition.
Qed.


(* Why obligation from file "swap0.mlw", characters 945-1014 *)
Lemma swap4_po_1 : 
  forall (a: Z),
  forall (b: Z),
  forall (tmp0: Z),
  forall (Post1: tmp0 = a),
  forall (a0: Z),
  forall (Post2: a0 = b),
  forall (b0: Z),
  forall (Post3: b0 = tmp0),
  a0 = b /\ b0 = a.
Proof.
intuition.
Qed.


(* Why obligation from file "swap0.mlw", characters 1109-1133 *)
Lemma test_swap4_po_1 : 
  forall (c: Z),
  forall (Post2: c = 1),
  forall (d: Z),
  forall (Post1: d = 2),
  forall (c1: Z),
  forall (d1: Z),
  forall (Post4: c1 = d /\ d1 = c),
  d1 = 1.
 (* test_swap4_po_1 *)
Proof.
intuition.
Qed.


(* Why obligation from file "swap0.mlw", characters 1187-1218 *)
Lemma call_swap4_x_y_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (Pre1: x = 3),
  forall (x0: Z),
  forall (y0: Z),
  forall (Post1: x0 = y /\ y0 = x),
  y0 = 3.
Proof.
intuition.
Qed.


(* Why obligation from file "swap0.mlw", characters 1240-1271 *)
Lemma call_swap4_y_x_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (Pre1: x = 3),
  forall (y0: Z),
  forall (x0: Z),
  forall (Post1: y0 = x /\ x0 = y),
  y0 = 3.
Proof.
intuition.
Qed.


