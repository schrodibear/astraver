
Require Import Why.
Require Import Omega.
Require Import ZArithRing.

(* Why obligation from file "peano.mlw", characters 272-301 *)
Lemma add1_po_1 : 
  forall (y: Z),
  forall (x: Z),
  forall (Pre3: y >= 0),
  forall (z: Z),
  forall (Post3: z = y),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (z1: Z),
  forall (Pre2: Variant1 = z1),
  forall (I: 0 <= z1 /\ x0 = (x + (y - z1))),
  forall (Test2: z1 > 0),
  forall (x1: Z),
  forall (Post1: x1 = (x0 + 1)),
  forall (z2: Z),
  forall (Post2: z2 = (z1 - 1)),
  (0 <= z2 /\ x1 = (x + (y - z2))) /\ (Zwf 0 z2 z1).
 Proof.
 unfold Zwf; intros; omega.
Qed.

(* Why obligation from file "peano.mlw", characters 178-309 *)
Lemma add1_po_2 : 
  forall (y: Z),
  forall (x: Z),
  forall (Pre3: y >= 0),
  forall (z: Z),
  forall (Post3: z = y),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (z1: Z),
  forall (Pre2: Variant1 = z1),
  forall (I: 0 <= z1 /\ x0 = (x + (y - z1))),
  forall (Test1: z1 <= 0),
  x0 = (x + y).
Proof.
unfold Zwf; intros; omega.
Qed.

(* Why obligation from file "peano.mlw", characters 211-247 *)
Lemma add1_po_3 : 
  forall (y: Z),
  forall (x: Z),
  forall (Pre3: y >= 0),
  forall (z: Z),
  forall (Post3: z = y),
  0 <= z /\ x = (x + (y - z)).
Proof.
intuition.
Qed.


(* Why obligation from file "peano.mlw", characters 367-391 *)
Lemma u1_po_1 : 
  forall (r: Z),
  forall (Post1: r = 3),
  7 >= 0.
 Proof.
 intros; omega.
 Qed.

(* Why obligation from file "peano.mlw", characters 367-391 *)
Lemma u1_po_2 : 
  forall (r: Z),
  forall (Post1: r = 3),
  forall (Pre1: 7 >= 0),
  forall (r1: Z),
  forall (Post3: r1 = (r + 7)),
  r1 = 10.
 Proof.
 intros; omega.
 Qed.


(* Why obligation from file "peano.mlw", characters 527-545 *)
Lemma rec_add1_po_1 : 
  forall (y: Z),
  forall (Pre8: y >= 0),
  forall (Variant1: Z),
  forall (y0: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = y0),
  forall (Pre6: y0 >= 0),
  forall (Test2: 0 < y0),
  forall (x1: Z),
  forall (Post3: x1 = (x0 + 1)),
  (y0 - 1) >= 0.
Proof.
intros; omega.
Qed.

(* Why obligation from file "peano.mlw", characters 480-567 *)
Lemma rec_add1_po_2 : 
  forall (y: Z),
  forall (Pre8: y >= 0),
  forall (Variant1: Z),
  forall (y0: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = y0),
  forall (Pre6: y0 >= 0),
  forall (Test2: 0 < y0),
  forall (x1: Z),
  forall (Post3: x1 = (x0 + 1)),
  forall (Pre5: (y0 - 1) >= 0),
  forall (Pre3: (y0 - 1) >= 0),
  forall (Pre4: (y0 - 1) >= 0),
  (Zwf 0 (y0 - 1) Variant1).
Proof.
intros; unfold Zwf; omega.
Qed.

(* Why obligation from file "peano.mlw", characters 508-549 *)
Lemma rec_add1_po_3 : 
  forall (y: Z),
  forall (Pre8: y >= 0),
  forall (Variant1: Z),
  forall (y0: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = y0),
  forall (Pre6: y0 >= 0),
  forall (Test2: 0 < y0),
  forall (x1: Z),
  forall (Post3: x1 = (x0 + 1)),
  forall (Pre5: (y0 - 1) >= 0),
  forall (x2: Z),
  forall (Post8: x2 = (x1 + (y0 - 1))),
  x2 = (x0 + y0).
Proof.
intros; omega.
Qed.

(* Why obligation from file "peano.mlw", characters 549-549 *)
Lemma rec_add1_po_4 : 
  forall (y: Z),
  forall (Pre8: y >= 0),
  forall (Variant1: Z),
  forall (y0: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = y0),
  forall (Pre6: y0 >= 0),
  forall (Test1: 0 >= y0),
  x0 = (x0 + y0).
Proof.
intros; omega.
Qed.


(* Why obligation from file "peano.mlw", characters 608-636 *)
Lemma u11_po_1 : 
  forall (r: Z),
  forall (Post1: r = 3),
  7 >= 0.
Proof.
intros; omega.
Qed.

(* Why obligation from file "peano.mlw", characters 608-636 *)
Lemma u11_po_2 : 
  forall (r: Z),
  forall (Post1: r = 3),
  forall (Pre1: 7 >= 0),
  forall (r1: Z),
  forall (Post3: r1 = (r + 7)),
  r1 = 10.
Proof.
intros; omega.
Qed.


(* Why obligation from file "peano.mlw", characters 933-947 *)
Lemma mult1_po_1 : 
  forall (y: Z),
  forall (x: Z),
  forall (Pre6: x >= 0 /\ y >= 0),
  forall (z: Z),
  forall (Post4: z = y),
  forall (savex: Z),
  forall (Post3: savex = x),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (Variant1: Z),
  forall (x1: Z),
  forall (z1: Z),
  forall (Pre5: Variant1 = z1),
  forall (I: 0 <= z1 /\ x1 = (x * (y - z1))),
  forall (Test2: z1 > 0),
  savex >= 0.
Proof.
intros; omega.
Qed.

(* Why obligation from file "peano.mlw", characters 933-967 *)
Lemma mult1_po_2 : 
  forall (y: Z),
  forall (x: Z),
  forall (Pre6: x >= 0 /\ y >= 0),
  forall (z: Z),
  forall (Post4: z = y),
  forall (savex: Z),
  forall (Post3: savex = x),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (Variant1: Z),
  forall (x1: Z),
  forall (z1: Z),
  forall (Pre5: Variant1 = z1),
  forall (I: 0 <= z1 /\ x1 = (x * (y - z1))),
  forall (Test2: z1 > 0),
  forall (Pre4: savex >= 0),
  forall (x2: Z),
  forall (Post14: x2 = (x1 + savex)),
  forall (z2: Z),
  forall (Post2: z2 = (z1 - 1)),
  (0 <= z2 /\ x2 = (x * (y - z2))) /\ (Zwf 0 z2 z1).
Proof.
simpl; intros.
repeat split; unfold Zwf; try omega.
subst z2 x2 savex.
decompose [and] I.
subst x1.
ring.
Qed.

(* Why obligation from file "peano.mlw", characters 833-977 *)
Lemma mult1_po_3 : 
  forall (y: Z),
  forall (x: Z),
  forall (Pre6: x >= 0 /\ y >= 0),
  forall (z: Z),
  forall (Post4: z = y),
  forall (savex: Z),
  forall (Post3: savex = x),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (Variant1: Z),
  forall (x1: Z),
  forall (z1: Z),
  forall (Pre5: Variant1 = z1),
  forall (I: 0 <= z1 /\ x1 = (x * (y - z1))),
  forall (Test1: z1 <= 0),
  x1 = (x * y).
 Proof.
 simpl; intros.
cut (z1 = 0%Z).
intros eq; rewrite eq in I.
 intuition.
generalize H2.
 ring (x * (y - 0))%Z.
 intro; ring; assumption.
omega.
Qed.

(* Why obligation from file "peano.mlw", characters 868-904 *)
Lemma mult1_po_4 : 
  forall (y: Z),
  forall (x: Z),
  forall (Pre6: x >= 0 /\ y >= 0),
  forall (z: Z),
  forall (Post4: z = y),
  forall (savex: Z),
  forall (Post3: savex = x),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  0 <= z /\ x0 = (x * (y - z)).
 Proof.
 intros.
subst z; split; [ omega | ring ]; assumption.
Qed.


(* Why obligation from file "peano.mlw", characters 1042-1067 *)
Lemma u2_po_1 : 
  forall (r: Z),
  forall (Post1: r = 4),
  r >= 0 /\ 6 >= 0.
 Proof.
 intros; omega.
 Qed.

(* Why obligation from file "peano.mlw", characters 1042-1067 *)
Lemma u2_po_2 : 
  forall (r: Z),
  forall (Post1: r = 4),
  forall (Pre1: r >= 0 /\ 6 >= 0),
  forall (r1: Z),
  forall (Post3: r1 = (r * 6)),
  r1 = 24.
 Proof.
 intros; omega.
 Qed.


(* Why obligation from file "peano.mlw", characters 1344-1345 *)
Lemma mult2_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (Pre18: x >= 0 /\ y >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (Pre17: Variant1 = x0),
  forall (Pre16: x0 >= 0 /\ y0 >= 0),
  forall (Test4: x0 = 0),
  0 = (x0 * y0).
Proof.
intros; subst; intuition.
Save.

(* Why obligation from file "peano.mlw", characters 1359-1374 *)
Lemma mult2_po_2 : 
  forall (x: Z),
  forall (y: Z),
  forall (Pre18: x >= 0 /\ y >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (Pre17: Variant1 = x0),
  forall (Pre16: x0 >= 0 /\ y0 >= 0),
  forall (Test3: x0 <> 0),
  (x0 - 1) >= 0 /\ y0 >= 0.
Proof.
intuition.
Save.

(* Why obligation from file "peano.mlw", characters 1185-1391 *)
Lemma mult2_po_3 : 
  forall (x: Z),
  forall (y: Z),
  forall (Pre18: x >= 0 /\ y >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (Pre17: Variant1 = x0),
  forall (Pre16: x0 >= 0 /\ y0 >= 0),
  forall (Test3: x0 <> 0),
  forall (Pre15: (x0 - 1) >= 0 /\ y0 >= 0),
  forall (Pre11: (x0 - 1) >= 0 /\ y0 >= 0),
  forall (Pre12: (x0 - 1) >= 0 /\ y0 >= 0),
  (Zwf 0 (x0 - 1) Variant1).
Proof.
intuition.
Save.

(* Why obligation from file "peano.mlw", characters 1351-1375 *)
Lemma mult2_po_4 : 
  forall (x: Z),
  forall (y: Z),
  forall (Pre18: x >= 0 /\ y >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (Pre17: Variant1 = x0),
  forall (Pre16: x0 >= 0 /\ y0 >= 0),
  forall (Test3: x0 <> 0),
  forall (Pre15: (x0 - 1) >= 0 /\ y0 >= 0),
  forall (aux_3: Z),
  forall (Post10: aux_3 = ((x0 - 1) * y0)),
  y0 >= 0.
Proof.
intuition.
Save.

(* Why obligation from file "peano.mlw", characters 1282-1283 *)
Lemma mult2_po_5 : 
  forall (x: Z),
  forall (y: Z),
  forall (Pre18: x >= 0 /\ y >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (Pre17: Variant1 = x0),
  forall (Pre16: x0 >= 0 /\ y0 >= 0),
  forall (Test3: x0 <> 0),
  forall (Pre15: (x0 - 1) >= 0 /\ y0 >= 0),
  forall (aux_3: Z),
  forall (Post10: aux_3 = ((x0 - 1) * y0)),
  forall (Pre13: y0 >= 0),
  forall (Pre14: y0 >= 0),
  forall (Variant3: Z),
  forall (a0: Z),
  forall (b0: Z),
  forall (Pre8: Variant3 = a0),
  forall (Pre7: a0 >= 0),
  forall (Test2: a0 = 0),
  b0 = (a0 + b0).
Proof.
intuition.
Save.

(* Why obligation from file "peano.mlw", characters 1289-1307 *)
Lemma mult2_po_6 : 
  forall (x: Z),
  forall (y: Z),
  forall (Pre18: x >= 0 /\ y >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (Pre17: Variant1 = x0),
  forall (Pre16: x0 >= 0 /\ y0 >= 0),
  forall (Test3: x0 <> 0),
  forall (Pre15: (x0 - 1) >= 0 /\ y0 >= 0),
  forall (aux_3: Z),
  forall (Post10: aux_3 = ((x0 - 1) * y0)),
  forall (Pre13: y0 >= 0),
  forall (Pre14: y0 >= 0),
  forall (Variant3: Z),
  forall (a0: Z),
  forall (Pre8: Variant3 = a0),
  forall (Pre7: a0 >= 0),
  forall (Test1: a0 <> 0),
  (a0 - 1) >= 0.
Proof.
intuition.
Save.

(* Why obligation from file "peano.mlw", characters 1261-1322 *)
Lemma mult2_po_7 : 
  forall (x: Z),
  forall (y: Z),
  forall (Pre18: x >= 0 /\ y >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (Pre17: Variant1 = x0),
  forall (Pre16: x0 >= 0 /\ y0 >= 0),
  forall (Test3: x0 <> 0),
  forall (Pre15: (x0 - 1) >= 0 /\ y0 >= 0),
  forall (aux_3: Z),
  forall (Post10: aux_3 = ((x0 - 1) * y0)),
  forall (Pre13: y0 >= 0),
  forall (Pre14: y0 >= 0),
  forall (Variant3: Z),
  forall (a0: Z),
  forall (Pre8: Variant3 = a0),
  forall (Pre7: a0 >= 0),
  forall (Test1: a0 <> 0),
  forall (Pre6: (a0 - 1) >= 0),
  forall (Pre4: (a0 - 1) >= 0),
  forall (Pre5: (a0 - 1) >= 0),
  (Zwf 0 (a0 - 1) Variant3).
Proof.
intuition.
Save.

(* Why obligation from file "peano.mlw", characters 1289-1307 *)
Lemma mult2_po_8 : 
  forall (x: Z),
  forall (y: Z),
  forall (Pre18: x >= 0 /\ y >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (Pre17: Variant1 = x0),
  forall (Pre16: x0 >= 0 /\ y0 >= 0),
  forall (Test3: x0 <> 0),
  forall (Pre15: (x0 - 1) >= 0 /\ y0 >= 0),
  forall (aux_3: Z),
  forall (Post10: aux_3 = ((x0 - 1) * y0)),
  forall (Pre13: y0 >= 0),
  forall (Pre14: y0 >= 0),
  forall (Variant3: Z),
  forall (a0: Z),
  forall (b0: Z),
  forall (Pre8: Variant3 = a0),
  forall (Pre7: a0 >= 0),
  forall (Test1: a0 <> 0),
  forall (Pre6: (a0 - 1) >= 0),
  forall (result0_0: Z),
  forall (Post4: result0_0 = (a0 - 1 + (b0 + 1))),
  result0_0 = (a0 + b0).
Proof.
intuition; subst; ring.
Save.

(* Why obligation from file "peano.mlw", characters 1351-1375 *)
Lemma mult2_po_9 : 
  forall (x: Z),
  forall (y: Z),
  forall (Pre18: x >= 0 /\ y >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (Pre17: Variant1 = x0),
  forall (Pre16: x0 >= 0 /\ y0 >= 0),
  forall (Test3: x0 <> 0),
  forall (Pre15: (x0 - 1) >= 0 /\ y0 >= 0),
  forall (aux_3: Z),
  forall (Post10: aux_3 = ((x0 - 1) * y0)),
  forall (Pre13: y0 >= 0),
  forall (result0: Z),
  forall (Post12: result0 = (y0 + aux_3)),
  result0 = (x0 * y0).
Proof.
intuition; subst; ring.
Save.

