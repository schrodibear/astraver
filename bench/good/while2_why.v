
Require Why.
Require Omega.




Lemma test_po_1 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with datatypes.
Save.

Lemma test_po_2 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = `10 - x0`)
  (Pre2: `x0 <= 10`)
  (Test2: `x0 < 10`)
  (x1: Z)
  (Post1: x1 = `x0 + 1`)
  `x1 <= 10` /\ (Zwf `0` `10 - x1` `10 - x0`).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma test_po_3 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = `10 - x0`)
  (Pre2: `x0 <= 10`)
  (Test2: `x0 < 10`)
  (x1: Z)
  (Post7: `x1 <= 10` /\ (Zwf `0` `10 - x1` `10 - x0`))
  (Zwf `0` `10 - x1` Variant1).
Proof.
Intros; Rewrite Pre3; Tauto.
Save.

Lemma test_po_4 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = `10 - x0`)
  (Pre2: `x0 <= 10`)
  (Test2: `x0 < 10`)
  (x1: Z)
  (Post7: `x1 <= 10` /\ (Zwf `0` `10 - x1` `10 - x0`))
  `x1 <= 10`.
Proof.
Intros; Intuition.
Save.

Lemma test_po_5 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = `10 - x0`)
  (Pre2: `x0 <= 10`)
  (Test1: `x0 >= 10`)
  x0 = `10`.
Proof.
Simpl; Intros; Omega.
Save.

Lemma test_po_6 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (x0: Z)
  (Post3: x0 = `10`)
  (Test4: `x0 > 0`)
  (x1: Z)
  (Post11: x1 = `(-x0)`)
  x1 = `(-10)`.
Proof.
Intros; Omega.
Save.

Lemma test_po_7 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (x0: Z)
  (Post3: x0 = `10`)
  (Test3: `x0 <= 0`)
  x0 = `(-10)`.
Proof.
Intros; Omega.
Save.

