
Require Omega.
Require Correctness.

Lemma add1_po_1 : 
  (y: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  (well_founded ? (Zwf ZERO)).
Proof. Auto with *. Save.

Lemma add1_po_2 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  (Variant1: Z) 
  (x0: Z) 
  (z0: Z) 
  `0 <= z0` /\
  x0 = `x + (y - z0)` ->
  Variant1 = z0 ->
  (result0: bool) 
  (if result0 then `z0 > 0` else `z0 <= 0`) ->
  (if true then `z0 > 0` else `z0 <= 0`) ->
  `0 <= z0` /\
  x0 = `x + (y - z0)` ->
  (x1: Z) 
  x1 = `x0 + 1` ->
  (z1: Z) 
  z1 = `z0 - 1` ->
  `0 <= z1` /\ x1 = `x + (y - z1)` /\ (Zwf `0` z1 z0).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma add1_po_3 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  (Variant1: Z) 
  (x0: Z) 
  (z0: Z) 
  `0 <= z0` /\
  x0 = `x + (y - z0)` ->
  Variant1 = z0 ->
  (result0: bool) 
  (if result0 then `z0 > 0` else `z0 <= 0`) ->
  (if true then `z0 > 0` else `z0 <= 0`) ->
  `0 <= z0` /\ x0 = `x + (y - z0)` ->
  (x1: Z) 
  (z1: Z) 
  `0 <= z1` /\ x1 = `x + (y - z1)` /\
  (Zwf `0` z1 z0) ->
  (Zwf `0` z1 Variant1).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma add1_po_4 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  (Variant1: Z) 
  (x0: Z) 
  (z0: Z) 
  `0 <= z0` /\
  x0 = `x + (y - z0)` ->
  Variant1 = z0 ->
  (result0: bool) 
  (if result0 then `z0 > 0` else `z0 <= 0`) ->
  (if true then `z0 > 0` else `z0 <= 0`) ->
  `0 <= z0` /\ x0 = `x + (y - z0)` ->
  (x1: Z) 
  (z1: Z) 
  `0 <= z1` /\ x1 = `x + (y - z1)` /\ (Zwf `0` z1 z0) ->
  `0 <= z1` /\ x1 = `x + (y - z1)`.
Proof. Intuition. Save.

Lemma add1_po_5 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  (Variant1: Z) 
  (x0: Z) 
  (z0: Z) 
  `0 <= z0` /\
  x0 = `x + (y - z0)` ->
  Variant1 = z0 ->
  (result0: bool) 
  (if result0 then `z0 > 0` else `z0 <= 0`) ->
  (if false then `z0 > 0` else `z0 <= 0`) ->
  `0 <= z0` /\ x0 = `x + (y - z0)` ->
  `0 <= z0` /\ x0 = `x + (y - z0)` /\
  ((if false then `z0 > 0` else `z0 <= 0`)).
Proof. Intuition. Save.

Lemma add1_po_6 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  `0 <= result` /\ x = `x + (y - result)`.
Proof. Intros; Omega. Save.

Lemma add1_po_7 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  (x0: Z) 
  (z0: Z) 
  `0 <= z0` /\ x0 = `x + (y - z0)` /\
  ((if false then `z0 > 0` else `z0 <= 0`)) ->
  x0 = `x + y`.
Proof. Intros; Omega. Save.
