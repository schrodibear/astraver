(* Load Programs. *)
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

(* Why obligation from file "peano.mlw", characters 211-247 *)
Lemma add1_po_2 : 
  forall (y: Z),
  forall (x: Z),
  forall (Pre3: y >= 0),
  forall (z: Z),
  forall (Post3: z = y),
  0 <= z /\ x = (x + (y - z)).
Proof.
unfold Zwf; intros; omega.
Qed.

(* Why obligation from file "peano.mlw", characters 158-309 *)
Lemma add1_po_3 : 
  forall (y: Z),
  forall (x: Z),
  forall (Pre3: y >= 0),
  forall (z: Z),
  forall (Post3: z = y),
  forall (x0: Z),
  forall (z1: Z),
  forall (I: (0 <= z1 /\ x0 = (x + (y - z1))) /\ z1 <= 0),
  x0 = (x + y).
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
  forall (Post9: x2 = (x1 + savex)),
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

(* Why obligation from file "peano.mlw", characters 868-904 *)
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
  0 <= z /\ x0 = (x * (y - z)).
 Proof.
 intros.
subst z; split; [ omega | ring ]; assumption.
Qed.

(* Why obligation from file "peano.mlw", characters 809-984 *)
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
  forall (x1: Z),
  forall (z1: Z),
  forall (I: (0 <= z1 /\ x1 = (x * (y - z1))) /\ z1 <= 0),
  x1 = (x * y).
 Proof.
 simpl; intros.
cut (z1 = 0%Z).
intros eq; rewrite eq in I.
 intuition.
generalize H4.
 ring (x * (y - 0))%Z.
 intro; ring; assumption.
omega.
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


