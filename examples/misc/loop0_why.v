
Require Why.
Require Omega.

Lemma p_po_1 : 
  (x: Z)
  (Pre6: `x >= 0`)
  (well_founded ? (Zwf ZERO)).
Proof. Auto with *. Save.

Lemma p_po_2 : 
  (x: Z)
  (Pre6: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre5: Variant1 = x0)
  (Pre4: `0 <= x0` /\ `x0 <= x`)
  (Test2: `x0 > 0`)
  `x0 >= 0`.
Proof.
Simpl; Intros; Omega.
Save.

Lemma p_po_3 : 
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
  `0 <= x1` /\ `x1 <= x` /\ (Zwf `0` x1 x0).
Proof.
Intros; Unfold Zwf; Intuition.
Save.

Lemma p_po_4 : 
  (x: Z)
  (Pre6: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre5: Variant1 = x0)
  (Pre4: `0 <= x0` /\ `x0 <= x`)
  (Test2: `x0 > 0`)
  (Pre3: `x0 >= 0`)
  (x1: Z)
  (Post5: `0 <= x1` /\ `x1 <= x` /\ (Zwf `0` x1 x0))
  (Zwf `0` x1 Variant1).
Proof. 
Intros; Rewrite Pre5; Intuition.
Save.

Lemma p_po_5 : 
  (x: Z)
  (Pre6: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre5: Variant1 = x0)
  (Pre4: `0 <= x0` /\ `x0 <= x`)
  (Test2: `x0 > 0`)
  (Pre3: `x0 >= 0`)
  (x1: Z)
  (Post5: `0 <= x1` /\ `x1 <= x` /\ (Zwf `0` x1 x0))
  `0 <= x1` /\ `x1 <= x`.
Proof.
Intuition.
Save.

Lemma p_po_6 : 
  (x: Z)
  (Pre6: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre5: Variant1 = x0)
  (Pre4: `0 <= x0` /\ `x0 <= x`)
  (Test1: `x0 <= 0`)
  `x0 >= 0`.
Proof.
Intros; Omega.
Save.

Lemma p_po_7 : 
  (x: Z)
  (Pre6: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre5: Variant1 = x0)
  (Pre4: `0 <= x0` /\ `x0 <= x`)
  (Test1: `x0 <= 0`)
  (Pre2: `x0 >= 0`)
  x0 = `0`.
Proof.
Intros; Omega.
Save.

Lemma p_po_8 : 
  (x: Z)
  (Pre6: `x >= 0`)
  `0 <= x` /\ `x <= x`.
Proof.
Intros; Omega.
Save.



