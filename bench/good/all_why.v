
Require Why.
Require Omega.

Lemma fc3_po_1 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  `result >= 0`.
Proof. Intros; Omega. Save.

Lemma arr1_po_1 : 
  `0 <= 0` /\ `0 < 10`.
Proof. Omega. Save.

Lemma arr2_po_1 : 
  `0 <= 1 + 2` /\ `1 + 2 < 10`.
Proof. Omega. Save.

Lemma arr3_po_1 : 
  (v4: Z)
  (Pre2: v4 = `0`)
  `0 <= v4` /\ `v4 < 10`.
Proof. Intros; Omega. Save.

Lemma arr4_po_1 : 
  (v6: (array `10` Z))
  (Pre3: (access v6 `0`) = `9`)
  `0 <= 0` /\ `0 < 10`.
Proof. Intros; Omega. Save.

Lemma arr4_po_2 : 
  (v6: (array `10` Z))
  (Pre3: (access v6 `0`) = `9`)
  (Pre2: `0 <= 0` /\ `0 < 10`)
  `0 <= (access v6 0)` /\ `(access v6 0) < 10`.
Proof. Intros; Omega. Save.

Lemma an2_po_1 : 
  (v4: Z)
  (Pre1: `v4 >= 0`)
  (v9: Z)
  (Post1: v9 = `v4 + 1`)
  `v9 > v4`.
Proof.
Intros; Omega.
Save.

Lemma an3_po_1 : 
  (v4: Z)
  (Pre1: `v4 >= 0`)
  (v9: Z)
  (Post1: v9 = `v4 + 1`)
  `v9 > v4`.
Proof.
Intros; Omega.
Save.

