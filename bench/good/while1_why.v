
Require Omega.
Require ProgWf.

Lemma p_po_1 : 
  (i: Z) 
  `i <= 10` ->
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with datatypes.
Save.

Lemma p_po_2 : 
  (i: Z) 
  `i <= 10` ->
  (Variant1: Z) 
  (i0: Z) 
  `i0 <= 10` ->
  Variant1 = `10 - i0` ->
  (result: bool) 
  (if result then `i0 < 10` else `i0 >= 10`) ->
  (if true then `i0 < 10` else `i0 >= 10`) ->
  `i0 <= 10` ->
  (i1: Z) 
  i1 = `i0 + 1` ->
  `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma p_po_3 : 
  (i: Z) 
  `i <= 10` ->
  (Variant1: Z) 
  (i0: Z) 
  `i0 <= 10` ->
  Variant1 = `10 - i0` ->
  (result: bool) 
  (if result then `i0 < 10` else `i0 >= 10`) ->
  (if true then `i0 < 10` else `i0 >= 10`) ->
  `i0 <= 10` ->
  (i1: Z) 
  `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`) ->
  (Zwf `0` `10 - i1` Variant1).
Proof. 
Intros. Rewrite H1; Tauto.
Save.

Lemma p_po_4 : 
  (i: Z) 
  `i <= 10` ->
  (Variant1: Z) 
  (i0: Z) 
  `i0 <= 10` ->
  Variant1 = `10 - i0` ->
  (result: bool) 
  (if result then `i0 < 10` else `i0 >= 10`) ->
  (if true then `i0 < 10` else `i0 >= 10`) ->
  `i0 <= 10` ->
  (i1: Z) 
  `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`) ->
  `i1 <= 10`.
Proof.
Intros. Simpl in H3; Omega.
Save.

Lemma p_po_5 : 
  (i: Z) 
  `i <= 10` ->
  (Variant1: Z) 
  (i0: Z) 
  `i0 <= 10` ->
  Variant1 = `10 - i0` ->
  (result: bool) 
  (if result then `i0 < 10` else `i0 >= 10`) ->
  (if false then `i0 < 10` else `i0 >= 10`) ->
  `i0 <= 10` ->
  i0 = `10`.
Proof.
Simpl; Intros; Omega.
Save.

