
Require Omega.
Require ProgWf.

Lemma p_po_1 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with datatypes.
Save.

Lemma p_po_2 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: `i0 <= 10`)
  (Pre4: Variant1 = `10 - i0`)
  (result: bool)
  (Bool1: (if result then `i0 < 10` else `i0 >= 10`))
  (Test2: (if true then `i0 < 10` else `i0 >= 10`))
  (Pre3: `i0 <= 10`)
  (i1: Z)
  (Post1: i1 = `i0 + 1`)
  `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma p_po_3 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: `i0 <= 10`)
  (Pre4: Variant1 = `10 - i0`)
  (result: bool)
  (Bool1: (if result then `i0 < 10` else `i0 >= 10`))
  (Test2: (if true then `i0 < 10` else `i0 >= 10`))
  (Pre3: `i0 <= 10`)
  (i1: Z)
  (Post5: `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`))
  (Zwf `0` `10 - i1` Variant1).
Proof. 
Intros. Rewrite Pre4; Tauto.
Save.

Lemma p_po_4 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: `i0 <= 10`)
  (Pre4: Variant1 = `10 - i0`)
  (result: bool)
  (Bool1: (if result then `i0 < 10` else `i0 >= 10`))
  (Test2: (if true then `i0 < 10` else `i0 >= 10`))
  (Pre3: `i0 <= 10`)
  (i1: Z)
  (Post5: `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`))
  `i1 <= 10`.
Proof.
Intros. Simpl in Test2; Omega.
Save.

Lemma p_po_5 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: `i0 <= 10`)
  (Pre4: Variant1 = `10 - i0`)
  (result: bool)
  (Bool1: (if result then `i0 < 10` else `i0 >= 10`))
  (Test1: (if false then `i0 < 10` else `i0 >= 10`))
  (Pre2: `i0 <= 10`)
  i0 = `10`.
Proof.
Simpl; Intros; Omega.
Save.

