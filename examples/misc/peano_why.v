
Require Why.
Require Omega.
Require ZArithRing.

(* Why obligation from file "peano.mlw", characters 178-309 *)
Lemma add1_po_1 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (z: Z)
  (Post3: z = y)
  (Variant1: Z)
  (x0: Z)
  (z1: Z)
  (Pre2: Variant1 = z1)
  (I: `0 <= z1` /\ `x0 = x + (y - z1)`)
  (Test2: `z1 > 0`)
  (x1: Z)
  (Post1: x1 = `x0 + 1`)
  (z2: Z)
  (Post2: z2 = `z1 - 1`)
  (`0 <= z2` /\ `x1 = x + (y - z2)`) /\ (Zwf `0` z2 z1).
Proof. 
Unfold Zwf; Intros; Omega.
Save.

(* Why obligation from file "peano.mlw", characters 211-247 *)
Lemma add1_po_2 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (z: Z)
  (Post3: z = y)
  `0 <= z` /\ `x = x + (y - z)`.
Proof.
Unfold Zwf; Intros; Omega.
Save.

(* Why obligation from file "peano.mlw", characters 158-309 *)
Lemma add1_po_3 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (z: Z)
  (Post3: z = y)
  (x0: Z)
  (z1: Z)
  (I: (`0 <= z1` /\ `x0 = x + (y - z1)`) /\ `z1 <= 0`)
  `x0 = x + y`.
Proof.
Intuition.
Save.


(* Why obligation from file "peano.mlw", characters 367-391 *)
Lemma u1_po_1 : 
  (r: Z)
  (Post1: r = `3`)
  `7 >= 0`.
Proof. Intros; Omega. Save.

(* Why obligation from file "peano.mlw", characters 367-391 *)
Lemma u1_po_2 : 
  (r: Z)
  (Post1: r = `3`)
  (Pre1: `7 >= 0`)
  (r1: Z)
  (Post3: `r1 = r + 7`)
  `r1 = 10`.
Proof. Intros; Omega. Save.


(* Why obligation from file "peano.mlw", characters 527-545 *)
Lemma rec_add1_po_1 : 
  (y: Z)
  (Pre8: `y >= 0`)
  (Variant1: Z)
  (y0: Z)
  (x0: Z)
  (Pre7: Variant1 = y0)
  (Pre6: `y0 >= 0`)
  (Test2: `0 < y0`)
  (x1: Z)
  (Post3: x1 = `x0 + 1`)
  `y0 - 1 >= 0`.
Proof.
Intros; Omega.
Save.

(* Why obligation from file "peano.mlw", characters 480-567 *)
Lemma rec_add1_po_2 : 
  (y: Z)
  (Pre8: `y >= 0`)
  (Variant1: Z)
  (y0: Z)
  (x0: Z)
  (Pre7: Variant1 = y0)
  (Pre6: `y0 >= 0`)
  (Test2: `0 < y0`)
  (x1: Z)
  (Post3: x1 = `x0 + 1`)
  (Pre5: `y0 - 1 >= 0`)
  (Pre3: `y0 - 1 >= 0`)
  (Pre4: `y0 - 1 >= 0`)
  (Zwf `0` `y0 - 1` Variant1).
Proof.
Intros; Unfold Zwf; Omega.
Save.

(* Why obligation from file "peano.mlw", characters 508-549 *)
Lemma rec_add1_po_3 : 
  (y: Z)
  (Pre8: `y >= 0`)
  (Variant1: Z)
  (y0: Z)
  (x0: Z)
  (Pre7: Variant1 = y0)
  (Pre6: `y0 >= 0`)
  (Test2: `0 < y0`)
  (x1: Z)
  (Post3: x1 = `x0 + 1`)
  (Pre5: `y0 - 1 >= 0`)
  (x2: Z)
  (Post8: `x2 = x1 + (y0 - 1)`)
  `x2 = x0 + y0`.
Proof.
Intros; Omega.
Save.

(* Why obligation from file "peano.mlw", characters 494-549 *)
Lemma rec_add1_po_4 : 
  (y: Z)
  (Pre8: `y >= 0`)
  (Variant1: Z)
  (y0: Z)
  (x0: Z)
  (Pre7: Variant1 = y0)
  (Pre6: `y0 >= 0`)
  (Test1: `0 >= y0`)
  `x0 = x0 + y0`.
Proof.
Intros; Omega.
Save.


(* Why obligation from file "peano.mlw", characters 608-636 *)
Lemma u11_po_1 : 
  (r: Z)
  (Post1: r = `3`)
  `7 >= 0`.
Proof.
Intros; Omega.
Save.

(* Why obligation from file "peano.mlw", characters 608-636 *)
Lemma u11_po_2 : 
  (r: Z)
  (Post1: r = `3`)
  (Pre1: `7 >= 0`)
  (r1: Z)
  (Post3: `r1 = r + 7`)
  `r1 = 10`.
Proof.
Intros; Omega.
Save.


(* Why obligation from file "peano.mlw", characters 933-947 *)
Lemma mult1_po_1 : 
  (y: Z)
  (x: Z)
  (Pre6: `x >= 0` /\ `y >= 0`)
  (z: Z)
  (Post4: z = y)
  (savex: Z)
  (Post3: savex = x)
  (x0: Z)
  (Post1: x0 = `0`)
  (Variant1: Z)
  (x1: Z)
  (z1: Z)
  (Pre5: Variant1 = z1)
  (I: `0 <= z1` /\ `x1 = x * (y - z1)`)
  (Test2: `z1 > 0`)
  `savex >= 0`.
Proof.
Intros; Omega.
Save.

(* Why obligation from file "peano.mlw", characters 833-977 *)
Lemma mult1_po_2 : 
  (y: Z)
  (x: Z)
  (Pre6: `x >= 0` /\ `y >= 0`)
  (z: Z)
  (Post4: z = y)
  (savex: Z)
  (Post3: savex = x)
  (x0: Z)
  (Post1: x0 = `0`)
  (Variant1: Z)
  (x1: Z)
  (z1: Z)
  (Pre5: Variant1 = z1)
  (I: `0 <= z1` /\ `x1 = x * (y - z1)`)
  (Test2: `z1 > 0`)
  (Pre4: `savex >= 0`)
  (x2: Z)
  (Post9: `x2 = x1 + savex`)
  (z2: Z)
  (Post2: z2 = `z1 - 1`)
  (`0 <= z2` /\ `x2 = x * (y - z2)`) /\ (Zwf `0` z2 z1).
Proof.
Simpl; Intros.
Repeat Split; Unfold Zwf; Try Omega.
Subst z2 x2 savex.
Decompose [and] I.
Subst x1.
Ring.
Save.

(* Why obligation from file "peano.mlw", characters 868-904 *)
Lemma mult1_po_3 : 
  (y: Z)
  (x: Z)
  (Pre6: `x >= 0` /\ `y >= 0`)
  (z: Z)
  (Post4: z = y)
  (savex: Z)
  (Post3: savex = x)
  (x0: Z)
  (Post1: x0 = `0`)
  `0 <= z` /\ `x0 = x * (y - z)`.
Proof. 
Intros.
Subst z; Split; [ Omega | Ring ]; Assumption.
Save.

(* Why obligation from file "peano.mlw", characters 809-984 *)
Lemma mult1_po_4 : 
  (y: Z)
  (x: Z)
  (Pre6: `x >= 0` /\ `y >= 0`)
  (z: Z)
  (Post4: z = y)
  (savex: Z)
  (Post3: savex = x)
  (x0: Z)
  (Post1: x0 = `0`)
  (x1: Z)
  (z1: Z)
  (I: (`0 <= z1` /\ `x1 = x * (y - z1)`) /\ `z1 <= 0`)
  `x1 = x * y`.
Proof. 
Simpl; Intros.
Cut `z1 = 0`.
Intros eq; Rewrite eq in I. Intuition.
Generalize H4. Ring `x*(y-0)`. Intro; Ring; Assumption.
Omega.
Save.


(* Why obligation from file "peano.mlw", characters 1042-1067 *)
Lemma u2_po_1 : 
  (r: Z)
  (Post1: r = `4`)
  `r >= 0` /\ `6 >= 0`.
Proof. Intros; Omega. Save.

(* Why obligation from file "peano.mlw", characters 1042-1067 *)
Lemma u2_po_2 : 
  (r: Z)
  (Post1: r = `4`)
  (Pre1: `r >= 0` /\ `6 >= 0`)
  (r1: Z)
  (Post3: `r1 = r * 6`)
  `r1 = 24`.
Proof. Intros; Omega. Save.


