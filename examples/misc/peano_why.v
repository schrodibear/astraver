
Require Omega.
Require Correctness.
Require ZArithRing.

Lemma add1_po_1 : 
  (y: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (well_founded ? (Zwf ZERO)).
Proof. Auto with *. Save.

Lemma add1_po_2 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (Variant1: Z)
  (z0: Z)
  (x0: Z)
  (I: `0 <= z0` /\ x0 = `x + (y - z0)`)
  (Pre2: Variant1 = z0)
  (result0: bool)
  (Bool1: (if result0 then `z0 > 0` else `z0 <= 0`))
  (Test2: `z0 > 0`)
  (x1: Z)
  (Post2: x1 = `x0 + 1`)
  (z1: Z)
  (Post3: z1 = `z0 - 1`)
  `0 <= z1` /\ x1 = `x + (y - z1)` /\ (Zwf `0` z1 z0).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma add1_po_3 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (Variant1: Z)
  (z0: Z)
  (x0: Z)
  (I: `0 <= z0` /\ x0 = `x + (y - z0)`)
  (Pre2: Variant1 = z0)
  (result0: bool)
  (Bool1: (if result0 then `z0 > 0` else `z0 <= 0`))
  (Test2: `z0 > 0`)
  (x1: Z)
  (z1: Z)
  (I: `0 <= z1` /\ x1 = `x + (y - z1)` /\ (Zwf `0` z1 z0))
  (Zwf `0` z1 Variant1).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma add1_po_4 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (Variant1: Z)
  (z0: Z)
  (x0: Z)
  (I: `0 <= z0` /\ x0 = `x + (y - z0)`)
  (Pre2: Variant1 = z0)
  (result0: bool)
  (Bool1: (if result0 then `z0 > 0` else `z0 <= 0`))
  (Test2: `z0 > 0`)
  (x1: Z)
  (z1: Z)
  (I: `0 <= z1` /\ x1 = `x + (y - z1)` /\ (Zwf `0` z1 z0))
  `0 <= z1` /\ x1 = `x + (y - z1)`.
Proof. Intuition. Save.

Lemma add1_po_5 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (Variant1: Z)
  (z0: Z)
  (x0: Z)
  (I: `0 <= z0` /\ x0 = `x + (y - z0)`)
  (Pre2: Variant1 = z0)
  (result0: bool)
  (Bool1: (if result0 then `z0 > 0` else `z0 <= 0`))
  (Test1: `z0 <= 0`)
  `0 <= z0` /\ x0 = `x + (y - z0)` /\ `z0 <= 0`.
Proof. Intuition. Save.

Lemma add1_po_6 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  `0 <= result` /\ x = `x + (y - result)`.
Proof. Intros; Omega. Save.

Lemma add1_po_7 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (x0: Z)
  (z0: Z)
  (I: `0 <= z0` /\ x0 = `x + (y - z0)` /\ `z0 <= 0`)
  x0 = `x + y`.
Proof. Intros; Omega. Save.

Lemma u1_po_1 : 
  (result: Z)
  (Post1: result = `3`)
  `7 >= 0`.
Proof. Intros; Omega. Save.

Lemma u1_po_2 : 
  (result: Z)
  (Post1: result = `3`)
  (Pre1: `7 >= 0`)
  (r0: Z)
  (Post3: r0 = `result + 7`)
  r0 = `10`.
Proof. Intros; Omega. Save.

Lemma mult1_po_1 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (result0: Z)
  (Post2: result0 = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (well_founded ? (Zwf ZERO)).
Proof. Auto with *. Save.

Lemma mult1_po_2 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (result0: Z)
  (Post2: result0 = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (Variant1: Z)
  (z0: Z)
  (x1: Z)
  (I: `0 <= z0` /\ x1 = `x * (y - z0)`)
  (Pre3: Variant1 = z0)
  (result2: bool)
  (Bool1: (if result2 then `z0 > 0` else `z0 <= 0`))
  (Test2: `z0 > 0`)
  `result0 >= 0`.
Proof.
Intros; Omega.
Save.

Lemma mult1_po_3 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (result0: Z)
  (Post2: result0 = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (Variant1: Z)
  (z0: Z)
  (x1: Z)
  (I: `0 <= z0` /\ x1 = `x * (y - z0)`)
  (Pre3: Variant1 = z0)
  (result2: bool)
  (Bool1: (if result2 then `z0 > 0` else `z0 <= 0`))
  (Test2: `z0 > 0`)
  (x2: Z)
  (Post8: x2 = `x1 + result0`)
  (z1: Z)
  (Post4: z1 = `z0 - 1`)
  `0 <= z1` /\ x2 = `x * (y - z1)` /\ (Zwf `0` z1 z0).
Proof. 
Simpl; Intros.
Repeat Split; Unfold Zwf; Try Omega.
Rewrite Post4; Clear Post4.
Rewrite Post8; Clear Post8.
Rewrite Post2; Clear Post2.
Decompose [and] I.
Rewrite H0; Clear H0.
Ring.
Save.

Lemma mult1_po_4 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (result0: Z)
  (Post2: result0 = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (Variant1: Z)
  (z0: Z)
  (x1: Z)
  (I: `0 <= z0` /\ x1 = `x * (y - z0)`)
  (Pre3: Variant1 = z0)
  (result2: bool)
  (Bool1: (if result2 then `z0 > 0` else `z0 <= 0`))
  (Test2: `z0 > 0`)
  (x2: Z)
  (z1: Z)
  (I: `0 <= z1` /\ x2 = `x * (y - z1)` /\ (Zwf `0` z1 z0))
  (Zwf `0` z1 Variant1).
Proof. 
Simpl; Intros.
Rewrite Pre3; Tauto.
Save.

Lemma mult1_po_5 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (result0: Z)
  (Post2: result0 = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (Variant1: Z)
  (z0: Z)
  (x1: Z)
  (I: `0 <= z0` /\ x1 = `x * (y - z0)`)
  (Pre3: Variant1 = z0)
  (result2: bool)
  (Bool1: (if result2 then `z0 > 0` else `z0 <= 0`))
  (Test2: `z0 > 0`)
  (x2: Z)
  (z1: Z)
  (I: `0 <= z1` /\ x2 = `x * (y - z1)` /\ (Zwf `0` z1 z0))
  `0 <= z1` /\ x2 = `x * (y - z1)`.
Proof.
Tauto.
Save.

Lemma mult1_po_6 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (result0: Z)
  (Post2: result0 = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (Variant1: Z)
  (z0: Z)
  (x1: Z)
  (I: `0 <= z0` /\ x1 = `x * (y - z0)`)
  (Pre3: Variant1 = z0)
  (result2: bool)
  (Bool1: (if result2 then `z0 > 0` else `z0 <= 0`))
  (Test1: `z0 <= 0`)
  `0 <= z0` /\ x1 = `x * (y - z0)` /\ `z0 <= 0`.
Proof. Tauto. Save.

Lemma mult1_po_7 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (result0: Z)
  (Post2: result0 = x)
  (x0: Z)
  (Post3: x0 = `0`)
  `0 <= result` /\ x0 = `x * (y - result)`.
Proof. Intros.
Rewrite Post1; Split; [ Omega | Ring ]; Assumption.
Save.

Lemma mult1_po_8 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (result0: Z)
  (Post2: result0 = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (x1: Z)
  (z0: Z)
  (I: `0 <= z0` /\ x1 = `x * (y - z0)` /\ `z0 <= 0`)
  x1 = `x * y`.
Proof.
Simpl; Intros.
Cut `z0 = 0`.
Intros eq; Rewrite eq in I. Decompose [and] I.
Generalize H1. Ring `x*(y-0)`. Intro; Ring; Assumption.
Omega.
Save.

Lemma u2_po_1 : 
  (result: Z)
  (Post1: result = `4`)
  `result >= 0` /\ `6 >= 0`.
Proof. Intros; Omega. Save.

Lemma u2_po_2 : 
  (result: Z)
  (Post1: result = `4`)
  (Pre1: `result >= 0` /\ `6 >= 0`)
  (r0: Z)
  (Post3: r0 = `result * 6`)
  r0 = `24`.
Proof. Intros; Omega. Save.

