
Require Omega.
Require Correctness.

Lemma p_po_1 : 
  (x: Z) 
  `x >= 0` ->
  (well_founded ? (Zwf ZERO)).
Proof. Auto with *. Save.

Lemma p_po_2 : 
  (x: Z) 
  `x >= 0` ->
  (Variant1: Z) 
  (x0: Z) 
  `0 <= x0` /\
  `x0 <= x` ->
  Variant1 = x0 ->
  (result: bool) 
  (if result then `x0 > 0` else `x0 <= 0`) ->
  (if true then `x0 > 0` else `x0 <= 0`) ->
  `0 <= x0` /\ `x0 <= x` ->
  (x1: Z) 
  x1 = `x0 - 1` ->
  `0 <= x1` /\ `x1 <= x` /\ (Zwf `0` x1 x0).
Proof.
Simpl; Unfold Zwf; Intros; Omega.
Save.

Lemma p_po_3 : 
  (x: Z) 
  `x >= 0` ->
  (Variant1: Z) 
  (x0: Z) 
  `0 <= x0` /\
  `x0 <= x` ->
  Variant1 = x0 ->
  (result: bool) 
  (if result then `x0 > 0` else `x0 <= 0`) ->
  (if true then `x0 > 0` else `x0 <= 0`) ->
  `0 <= x0` /\ `x0 <= x` ->
  (x1: Z) 
  `0 <= x1` /\ `x1 <= x` /\ (Zwf `0` x1 x0) ->
  (Zwf `0` x1 Variant1).
Proof.
Intros. Rewrite H1; Intuition.
Save.

Lemma p_po_4 : 
  (x: Z) 
  `x >= 0` ->
  (Variant1: Z) 
  (x0: Z) 
  `0 <= x0` /\
  `x0 <= x` ->
  Variant1 = x0 ->
  (result: bool) 
  (if result then `x0 > 0` else `x0 <= 0`) ->
  (if true then `x0 > 0` else `x0 <= 0`) ->
  `0 <= x0` /\ `x0 <= x` ->
  (x1: Z) 
  `0 <= x1` /\ `x1 <= x` /\ (Zwf `0` x1 x0) ->
  `0 <= x1` /\ `x1 <= x`.
Proof. Intuition. Save.

Lemma p_po_5 : 
  (x: Z) 
  `x >= 0` ->
  (Variant1: Z) 
  (x0: Z) 
  `0 <= x0` /\
  `x0 <= x` ->
  Variant1 = x0 ->
  (result: bool) 
  (if result then `x0 > 0` else `x0 <= 0`) ->
  (if false then `x0 > 0` else `x0 <= 0`) ->
  `0 <= x0` /\ `x0 <= x` ->
  x0 = `0`.
Proof.
Simpl; Intros; Omega.
Save.

Lemma p_po_6 : 
  (x: Z) 
  `x >= 0` ->
  `0 <= x` /\ `x <= x`.
Proof.
Intros; Omega.
Save.

