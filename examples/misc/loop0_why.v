
Require Why.
Require Omega.

(* Why obligation from file "loop0.mlw", characters 316-327 *)
Lemma p_po_1 : 
  (x: Z)
  (Pre4: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = x0)
  (Pre2: `0 <= x0` /\ `x0 <= x`)
  (Test2: `x0 > 0`)
  (x1: Z)
  (Post1: x1 = `x0 - 1`)
  (`0 <= x1` /\ `x1 <= x`) /\ (Zwf `0` x1 x0).
Proof. Intuition. Save.

(* Why obligation from file "loop0.mlw", characters 281-297 *)
Lemma p_po_2 : 
  (x: Z)
  (Pre4: `x >= 0`)
  `0 <= x` /\ `x <= x`.
Proof.
Intuition.
Save.

(* Why obligation from file "loop0.mlw", characters 227-348 *)
Lemma p_po_3 : 
  (x: Z)
  (Pre4: `x >= 0`)
  (x0: Z)
  (Post2: (`0 <= x0` /\ `x0 <= x`) /\ `x0 <= 0`)
  `x0 = 0`.
Proof.
Intuition.
Save.
