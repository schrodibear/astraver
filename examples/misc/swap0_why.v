Require Why.
Require Omega.

(* Why obligation from file "swap0.mlw", characters 149-174 *)
Lemma swap1_po_1 : 
  (x: Z)
  (y: Z)
  (t: Z)
  (Post3: t = x)
  (x0: Z)
  (Post1: x0 = y)
  (y0: Z)
  (Post2: y0 = t)
  `x0 = y` /\ `y0 = x`.
Proof.
Intuition.
Save.


(* Why obligation from file "swap0.mlw", characters 316-358 *)
Lemma swap2_po_1 : 
  (x: Z)
  (y: Z)
  (t: Z)
  (Post3: t = x)
  (x0: Z)
  (Post1: x0 = y)
  (y0: Z)
  (Post2: y0 = t)
  `x0 = y` /\ `y0 = x`.
Proof.
Intuition.
Save.


(* Why obligation from file "swap0.mlw", characters 509-534 *)
Lemma swap3_po_1 : 
  (a: Z)
  (b: Z)
  (t: Z)
  (Post3: t = a)
  (a0: Z)
  (Post1: a0 = b)
  (b0: Z)
  (Post2: b0 = t)
  `a0 = b` /\ `b0 = a`.
Proof.
Intuition.
Save.


(* Why obligation from file "swap0.mlw", characters 654-678 *)
Lemma test_swap3_po_1 : 
  (result: Z)
  (Post2: result = `1`)
  (result0: Z)
  (Post1: result0 = `2`)
  (c0: Z)
  (d0: Z)
  (Post4: `c0 = result0` /\ `d0 = result`)
  `d0 = 1`.
Proof. (* test_swap3_po_1 *)
Intuition.
Save.



(* Why obligation from file "swap0.mlw", characters 790-826 *)
Lemma call_swap3_y_x_po_1 : 
  (x: Z)
  (y: Z)
  (y0: Z)
  (x0: Z)
  (Post1: `y0 = x` /\ `x0 = y`)
  `x0 = y` /\ `y0 = x`.
Proof. (* call_swap3_y_x_po_1 *)
Intuition.
Save.


(* Why obligation from file "swap0.mlw", characters 945-1014 *)
Lemma swap4_po_1 : 
  (a: Z)
  (b: Z)
  (tmp0: Z)
  (Post1: tmp0 = a)
  (a0: Z)
  (Post2: a0 = b)
  (b0: Z)
  (Post3: b0 = tmp0)
  `a0 = b` /\ `b0 = a`.
Proof.
Intuition.
Save.


(* Why obligation from file "swap0.mlw", characters 1109-1133 *)
Lemma test_swap4_po_1 : 
  (result: Z)
  (Post2: result = `1`)
  (result0: Z)
  (Post1: result0 = `2`)
  (c0: Z)
  (d0: Z)
  (Post4: `c0 = result0` /\ `d0 = result`)
  `d0 = 1`.
Proof. (* test_swap4_po_1 *)
Intuition.
Save.


(* Why obligation from file "swap0.mlw", characters 1187-1218 *)
Lemma call_swap4_x_y_po_1 : 
  (x: Z)
  (y: Z)
  (Pre1: `x = 3`)
  (x0: Z)
  (y0: Z)
  (Post1: `x0 = y` /\ `y0 = x`)
  `y0 = 3`.
Proof.
Intuition.
Save.


(* Why obligation from file "swap0.mlw", characters 1240-1271 *)
Lemma call_swap4_y_x_po_1 : 
  (x: Z)
  (y: Z)
  (Pre1: `x = 3`)
  (y0: Z)
  (x0: Z)
  (Post1: `y0 = x` /\ `x0 = y`)
  `y0 = 3`.
Proof.
Intuition.
Save.


