
Require Why.
Require Omega.

(* Why obligation from file "loop0.mlw", characters 229-235 *)
Lemma p_po_1 : 
  (x: Z)
  (Pre6: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre5: Variant1 = x0)
  (Pre4: `0 <= x0` /\ `x0 <= x`)
  (Test2: `x0 > 0`)
  `x0 >= 0`.
Proof. Auto with *. Save.

(* Why obligation from file "loop0.mlw", characters 240-327 *)
Lemma p_po_2 : 
  (x: Z)
  (Pre6: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre5: Variant1 = x0)
  (Pre4: `0 <= x0` /\ `x0 <= x`)
  (Test2: `x0 > 0`)
  (Pre3: `x0 >= 0`)
  (x1: Z)
  (Post1: x1 = `x0 - 1`)
  (`0 <= x1` /\ `x1 <= x`) /\ (Zwf `0` x1 x0).
Proof.
Intros; Unfold Zwf; Intuition.
Save.

(* Why obligation from file "loop0.mlw", characters 229-235 *)
Lemma p_po_3 : 
  (x: Z)
  (Pre6: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre5: Variant1 = x0)
  (Pre4: `0 <= x0` /\ `x0 <= x`)
  (Test1: `x0 <= 0`)
  `x0 >= 0`.
Proof.
Intuition.
Save.

(* Why obligation from file "loop0.mlw", characters 227-340 *)
Lemma p_po_4 : 
  (x: Z)
  (Pre6: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre5: Variant1 = x0)
  (Pre4: `0 <= x0` /\ `x0 <= x`)
  (Test1: `x0 <= 0`)
  (Pre2: `x0 >= 0`)
  `x0 = 0`.
Proof. 
Intros; Omega.
Save.

(* Why obligation from file "loop0.mlw", characters 273-289 *)
Lemma p_po_5 : 
  (x: Z)
  (Pre6: `x >= 0`)
  `0 <= x` /\ `x <= x`.
Proof.
Intros; Omega.
Save.


