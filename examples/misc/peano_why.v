
Require Omega.
Require Correctness.
Require ZArithRing.

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

Lemma u1_po_1 : 
  (result: Z) 
  result = `3` ->
  `7 >= 0`.
Proof. Intros; Omega. Save.

Lemma u1_po_2 : 
  (result: Z) 
  result = `3` ->
  `7 >= 0` ->
  (r0: Z) 
  r0 = `result + 7` ->
  r0 = `10`.
Proof. Intros; Omega. Save.

Lemma mult1_po_1 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  ((x0:Z)
   (x0 = `0` ->
    ((x0:Z)
     ((z:Z)
      (`0 <= z` /\ x0 = `x * (y - z)` /\
       ((if false then `z > 0` else `z <= 0`)) -> x0 = `x * y`))))).
Proof.
Simpl; Intros.
Decompose [and] H2; Clear H2.
Replace `x*y` with `x*(y-z)`; Try Assumption.
Cut `z=0`; Try Omega. Intro eq; Rewrite eq; Ring.
Save.

Lemma mult1_po_2 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  ((x0:Z)
   (x0 = `0` ->
    ((x0:Z)
     ((z:Z)
      (`0 <= z` /\ x0 = `x * (y - z)` /\
       ((if false then `z > 0` else `z <= 0`)) -> x0 = `x * y`))))) ->
  (x0: Z) 
  x0 = `0` ->
  (well_founded ? (Zwf ZERO)).
Proof. Auto with *. Save.

Lemma mult1_po_3 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  (result0: Z) 
  ((x0:Z)
   (x0 = `0` ->
    ((x0:Z)
     ((z:Z)
      (`0 <= z` /\ x0 = `x * (y - z)` /\
       ((if false then `z > 0` else `z <= 0`)) -> x0 = `x * y`))))) ->
  (x0: Z) 
  x0 = `0` ->
  (Variant3: Z) 
  (x1: Z) 
  (z0: Z) 
  `0 <= z0` /\
  x1 = `x * (y - z0)` ->
  Variant3 = z0 ->
  (result2: bool) 
  (if result2 then `z0 > 0` else `z0 <= 0`) ->
  (if true then `z0 > 0` else `z0 <= 0`) ->
  `0 <= z0` /\ x1 = `x * (y - z0)` ->
  `result0 >= 0`.
Proof. Simpl; Intros.

Lemma mult1_po_4 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  (result0: Z) 
  ((x0:Z)
   (x0 = `0` ->
    ((x0:Z)
     ((z:Z)
      (`0 <= z` /\ x0 = `x * (y - z)` /\
       ((if false then `z > 0` else `z <= 0`)) -> x0 = `x * y`))))) ->
  (x0: Z) 
  x0 = `0` ->
  (Variant3: Z) 
  (x1: Z) 
  (z0: Z) 
  `0 <= z0` /\
  x1 = `x * (y - z0)` ->
  Variant3 = z0 ->
  (result2: bool) 
  (if result2 then `z0 > 0` else `z0 <= 0`) ->
  (if true then `z0 > 0` else `z0 <= 0`) ->
  `0 <= z0` /\
  x1 = `x * (y - z0)` ->
  (x2: Z) 
  x2 = `x1 + result0` ->
  (z1: Z) 
  z1 = `z0 - 1` ->
  `0 <= z1` /\ x2 = `x * (y - z1)` /\ (Zwf `0` z1 z0).
Proof. Simpl; Intros.
Repeat Split; Unfold Zwf; Try Omega.
Rewrite H8; Clear H8.
Rewrite H1; Clear H1.
Rewrite H9; Clear H9.
Decompose [and] H7.
Rewrite H8; Clear H8.
Ring.


Lemma mult1_po_5 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  ((x0:Z)
   (x0 = `0` ->
    ((x0:Z)
     ((z:Z)
      (`0 <= z` /\ x0 = `x * (y - z)` /\
       ((if false then `z > 0` else `z <= 0`)) -> x0 = `x * y`))))) ->
  (x0: Z) 
  x0 = `0` ->
  (Variant3: Z) 
  (x1: Z) 
  (z0: Z) 
  `0 <= z0` /\
  x1 = `x * (y - z0)` ->
  Variant3 = z0 ->
  (result2: bool) 
  (if result2 then `z0 > 0` else `z0 <= 0`) ->
  (if true then `z0 > 0` else `z0 <= 0`) ->
  `0 <= z0` /\ x1 = `x * (y - z0)` ->
  (x2: Z) 
  (z1: Z) 
  `0 <= z1` /\ x2 = `x * (y - z1)` /\
  (Zwf `0` z1 z0) ->
  (Zwf `0` z1 Variant3).

Lemma mult1_po_6 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  ((x0:Z)
   (x0 = `0` ->
    ((x0:Z)
     ((z:Z)
      (`0 <= z` /\ x0 = `x * (y - z)` /\
       ((if false then `z > 0` else `z <= 0`)) -> x0 = `x * y`))))) ->
  (x0: Z) 
  x0 = `0` ->
  (Variant3: Z) 
  (x1: Z) 
  (z0: Z) 
  `0 <= z0` /\
  x1 = `x * (y - z0)` ->
  Variant3 = z0 ->
  (result2: bool) 
  (if result2 then `z0 > 0` else `z0 <= 0`) ->
  (if true then `z0 > 0` else `z0 <= 0`) ->
  `0 <= z0` /\ x1 = `x * (y - z0)` ->
  (x2: Z) 
  (z1: Z) 
  `0 <= z1` /\ x2 = `x * (y - z1)` /\ (Zwf `0` z1 z0) ->
  `0 <= z1` /\ x2 = `x * (y - z1)`.

Lemma mult1_po_7 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  ((x0:Z)
   (x0 = `0` ->
    ((x0:Z)
     ((z:Z)
      (`0 <= z` /\ x0 = `x * (y - z)` /\
       ((if false then `z > 0` else `z <= 0`)) -> x0 = `x * y`))))) ->
  (x0: Z) 
  x0 = `0` ->
  (Variant3: Z) 
  (x1: Z) 
  (z0: Z) 
  `0 <= z0` /\
  x1 = `x * (y - z0)` ->
  Variant3 = z0 ->
  (result2: bool) 
  (if result2 then `z0 > 0` else `z0 <= 0`) ->
  (if false then `z0 > 0` else `z0 <= 0`) ->
  `0 <= z0` /\ x1 = `x * (y - z0)` ->
  `0 <= z0` /\ x1 = `x * (y - z0)` /\
  ((if false then `z0 > 0` else `z0 <= 0`)).

Lemma mult1_po_8 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  ((x0:Z)
   (x0 = `0` ->
    ((x0:Z)
     ((z:Z)
      (`0 <= z` /\ x0 = `x * (y - z)` /\
       ((if false then `z > 0` else `z <= 0`)) -> x0 = `x * y`))))) ->
  (x0: Z) 
  x0 = `0` ->
  `0 <= result` /\ x0 = `x * (y - result)`.

Lemma mult1_po_9 : 
  (y: Z) 
  (x: Z) 
  `y >= 0` ->
  (result: Z) 
  result = y ->
  ((x0:Z)
   (x0 = `0` ->
    ((x0:Z)
     ((z:Z)
      (`0 <= z` /\ x0 = `x * (y - z)` /\
       ((if false then `z > 0` else `z <= 0`)) -> x0 = `x * y`))))) ->
  (x0: Z) 
  x0 = `0` ->
  (x1: Z) 
  (z0: Z) 
  `0 <= z0` /\ x1 = `x * (y - z0)` /\
  ((if false then `z0 > 0` else `z0 <= 0`)) ->
  x1 = `x * y`.

