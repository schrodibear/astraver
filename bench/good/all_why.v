
Require Why.
Require Omega.

Lemma p1_po_1 : 
  True.
Proof.
Tauto.
Save.

Lemma p2_po_1 : 
  ~False.
Proof.
Tauto.
Save.

Lemma p3_po_1 : 
  True /\ True.
Proof.
Tauto.
Save.

Lemma p4_po_1 : 
  True \/ False.
Proof.
Tauto.
Save.

Lemma p5_po_1 : 
  False \/ ~False.
Proof. 
Auto.
Save.

Lemma p6_po_1 : 
  (True -> ~False).
Proof.
Auto.
Save.

Lemma p7_po_1 : 
  ((x:Z) x = x).
Proof.
Auto.
Save.

Lemma p8_po_1 : 
  True /\ ((x:Z) x = x).
Proof.
Auto.
Save.

Lemma p9_po_1 : 
  ((x:Z) ((y:Z) (x = y -> x = y))).
Proof.
Auto.
Save.

Lemma arr1_po_1 : 
  `0 <= 0` /\ `0 < 10`.
Proof. (* arr1_po_1 *)
Omega.
Save.

Lemma arr2_po_1 : 
  `0 <= 1 + 2` /\ `1 + 2 < 10`.
Proof. (* arr2_po_1 *)
Omega.
Save.

Lemma arr3_po_1 : 
  (v4: Z)
  (Pre2: v4 = `0`)
  `0 <= v4` /\ `v4 < 10`.
Proof. (* arr3_po_1 *)
Intros; Omega.
Save.

Lemma arr4_po_1 : 
  (v6: (array `10` Z))
  (Pre3: (access v6 `0`) = `9`)
  `0 <= 0` /\ `0 < 10`.
Proof. (* arr4_po_1 *)
Intros; Omega.
Save.

Lemma arr4_po_2 : 
  (v6: (array `10` Z))
  (Pre3: (access v6 `0`) = `9`)
  (Pre2: `0 <= 0` /\ `0 < 10`)
  `0 <= (access v6 0)` /\ `(access v6 0) < 10`.
Proof. (* arr4_po_2 *)
Intros; Omega.
Save.

Lemma fc3_po_1 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  `result >= 0`.
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

