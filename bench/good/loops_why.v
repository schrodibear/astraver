
Require Why.
Require Omega.

Lemma loop1_po_1 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with datatypes.
Save.

Lemma loop1_po_2 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: Variant1 = `10 - i0`)
  (Pre4: `i0 <= 10`)
  (Test2: `i0 < 10`)
  (Pre3: `i0 <= 10`)
  (i1: Z)
  (Post1: i1 = `i0 + 1`)
  `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma loop1_po_3 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: Variant1 = `10 - i0`)
  (Pre4: `i0 <= 10`)
  (Test2: `i0 < 10`)
  (Pre3: `i0 <= 10`)
  (i1: Z)
  (Post2: `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`))
  (Zwf `0` `10 - i1` Variant1).
Proof.
Intros. Rewrite Pre5; Tauto.
Save.

Lemma loop1_po_4 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: Variant1 = `10 - i0`)
  (Pre4: `i0 <= 10`)
  (Test1: `i0 >= 10`)
  (Pre2: `i0 <= 10`)
  `i0 = 10`.
Proof.
Intros; Omega.
Save.



Lemma loop2_po_1 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with datatypes.
Save.

Lemma loop2_po_2 : 
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

Lemma loop2_po_3 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = `10 - x0`)
  (Pre2: `x0 <= 10`)
  (Test2: `x0 < 10`)
  (x1: Z)
  (Post3: `x1 <= 10` /\ (Zwf `0` `10 - x1` `10 - x0`))
  (Zwf `0` `10 - x1` Variant1).
Proof.
Intros; Rewrite Pre3; Tauto.
Save.

Lemma loop2_po_4 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = `10 - x0`)
  (Pre2: `x0 <= 10`)
  (Test1: `x0 >= 10`)
  `x0 = 10`.
Proof.
Intros; Intuition.
Save.

Lemma loop2_po_5 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (x0: Z)
  (Post4: `x0 = 10`)
  (Test4: `x0 > 0`)
  (x1: Z)
  (Post11: `x1 = (-x0)`)
  `x1 = (-10)`.
Proof.
Simpl; Intros; Omega.
Save.

Lemma loop2_po_6 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (x0: Z)
  (Post4: `x0 = 10`)
  (Test3: `x0 <= 0`)
  `x0 = (-10)`.
Proof.
Intros; Omega.
Save.


