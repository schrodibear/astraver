
Require Omega.
Require ProgWf.

Lemma test_po_1 : 
  (x: Z) 
  `x <= 10` ->
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with datatypes.
Save.

Lemma test_po_2 : 
  (x: Z) 
  `x <= 10` ->
  (Variant1: Z) 
  (x0: Z) 
  `x0 <= 10` ->
  Variant1 = `10 - x0` ->
  (result: bool) 
  (if result then `x0 < 10` else `x0 >= 10`) ->
  (if true then `x0 < 10` else `x0 >= 10`) ->
  `x0 <= 10` ->
  (x1: Z) 
  x1 = `x0 + 1` ->
  `x1 <= 10` /\ (Zwf `0` `10 - x1` `10 - x0`).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma test_po_3 : 
  (x: Z) 
  `x <= 10` ->
  (Variant1: Z) 
  (x0: Z) 
  `x0 <= 10` ->
  Variant1 = `10 - x0` ->
  (result: bool) 
  (if result then `x0 < 10` else `x0 >= 10`) ->
  (if true then `x0 < 10` else `x0 >= 10`) ->
  `x0 <= 10` ->
  (x1: Z) 
  `x1 <= 10` /\ (Zwf `0` `10 - x1` `10 - x0`) ->
  (Zwf `0` `10 - x1` Variant1).
Proof.
Intros; Rewrite H1; Tauto.
Save.

Lemma test_po_4 : 
  (x: Z) 
  `x <= 10` ->
  (Variant1: Z) 
  (x0: Z) 
  `x0 <= 10` ->
  Variant1 = `10 - x0` ->
  (result: bool) 
  (if result then `x0 < 10` else `x0 >= 10`) ->
  (if true then `x0 < 10` else `x0 >= 10`) ->
  `x0 <= 10` ->
  (x1: Z) 
  `x1 <= 10` /\ (Zwf `0` `10 - x1` `10 - x0`) ->
  `x1 <= 10`.
Proof.
Intros; Intuition.
Save.

Lemma test_po_5 : 
  (x: Z) 
  `x <= 10` ->
  (Variant1: Z) 
  (x0: Z) 
  `x0 <= 10` ->
  Variant1 = `10 - x0` ->
  (result: bool) 
  (if result then `x0 < 10` else `x0 >= 10`) ->
  (if false then `x0 < 10` else `x0 >= 10`) ->
  `x0 <= 10` ->
  x0 = `10`.
Proof.
Simpl; Intros; Omega.
Save.

Lemma test_po_6 : 
  (x: Z) 
  `x <= 10` ->
  (x0: Z) 
  x0 = `10` ->
  (result0: bool) 
  (if result0 then `x0 > 0` else `x0 <= 0`) ->
  (if true then `x0 > 0` else `x0 <= 0`) ->
  (x1: Z) 
  x1 = `-x0` ->
  x1 = `-10`.
Proof.
Simpl; Intros; Omega.
Save.

Lemma test_po_7 : 
  (x: Z) 
  `x <= 10` ->
  (x0: Z) 
  x0 = `10` ->
  (result0: bool) 
  (if result0 then `x0 > 0` else `x0 <= 0`) ->
  (if false then `x0 > 0` else `x0 <= 0`) ->
  x0 = `-10`.
Proof.
Simpl; Intros; Omega.
Save.

