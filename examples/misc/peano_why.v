(* Load Programs. *)
Require Import Why.
Require Import Omega.
Require Import ZArithRing.

(* Why obligation from file , characters 272-301 *)
Lemma add1_po_1 :
 forall (y x:Z) (Pre3:(y >= 0)%Z) (z:Z) (Post3:z = y)
   (Variant1 x0 z1:Z) (Pre2:Variant1 = z1)
   (I:(0 <= z1)%Z /\ x0 = (x + (y - z1))%Z) (Test2:(z1 > 0)%Z) 
   (x1:Z) (Post1:x1 = (x0 + 1)%Z) (z2:Z) (Post2:z2 = (z1 - 1)%Z),
   ((0 <= z2)%Z /\ x1 = (x + (y - z2))%Z) /\ Zwf 0 z2 z1.
 Proof.
 unfold Zwf; intros; omega.
Qed.

(* Why obligation from file , characters 211-247 *)
Lemma add1_po_2 :
 forall (y x:Z) (Pre3:(y >= 0)%Z) (z:Z) (Post3:z = y),
   (0 <= z)%Z /\ x = (x + (y - z))%Z.
Proof.
unfold Zwf; intros; omega.
Qed.

(* Why obligation from file , characters 158-309 *)
Lemma add1_po_3 :
 forall (y x:Z) (Pre3:(y >= 0)%Z) (z:Z) (Post3:z = y) (x0 z1:Z)
   (I:((0 <= z1)%Z /\ x0 = (x + (y - z1))%Z) /\ (z1 <= 0)%Z),
   x0 = (x + y)%Z.
Proof.
intuition.
Qed.


(* Why obligation from file , characters 367-391 *)
Lemma u1_po_1 : forall (r:Z) (Post1:r = 3%Z), (7 >= 0)%Z.
 Proof.
 intros; omega.
 Qed.

(* Why obligation from file , characters 367-391 *)
Lemma u1_po_2 :
 forall (r:Z) (Post1:r = 3%Z) (Pre1:(7 >= 0)%Z) (r1:Z)
   (Post3:r1 = (r + 7)%Z), r1 = 10%Z.
 Proof.
 intros; omega.
 Qed.


(* Why obligation from file , characters 527-545 *)
Lemma rec_add1_po_1 :
 forall (y:Z) (Pre8:(y >= 0)%Z) (Variant1 y0 x0:Z) (Pre7:Variant1 = y0)
   (Pre6:(y0 >= 0)%Z) (Test2:(0 < y0)%Z) (x1:Z)
   (Post3:x1 = (x0 + 1)%Z), (y0 - 1 >= 0)%Z.
Proof.
intros; omega.
Qed.

(* Why obligation from file , characters 480-567 *)
Lemma rec_add1_po_2 :
 forall (y:Z) (Pre8:(y >= 0)%Z) (Variant1 y0 x0:Z) (Pre7:Variant1 = y0)
   (Pre6:(y0 >= 0)%Z) (Test2:(0 < y0)%Z) (x1:Z) (Post3:x1 = (x0 + 1)%Z)
   (Pre5 Pre3 Pre4:(y0 - 1 >= 0)%Z), Zwf 0 (y0 - 1) Variant1.
Proof.
intros; unfold Zwf; omega.
Qed.

(* Why obligation from file , characters 508-549 *)
Lemma rec_add1_po_3 :
 forall (y:Z) (Pre8:(y >= 0)%Z) (Variant1 y0 x0:Z) (Pre7:Variant1 = y0)
   (Pre6:(y0 >= 0)%Z) (Test2:(0 < y0)%Z) (x1:Z) (Post3:x1 = (x0 + 1)%Z)
   (Pre5:(y0 - 1 >= 0)%Z) (x2:Z) (Post8:x2 = (x1 + (y0 - 1))%Z),
   x2 = (x0 + y0)%Z.
Proof.
intros; omega.
Qed.

(* Why obligation from file , characters 549-549 *)
Lemma rec_add1_po_4 :
 forall (y:Z) (Pre8:(y >= 0)%Z) (Variant1 y0 x0:Z) (Pre7:Variant1 = y0)
   (Pre6:(y0 >= 0)%Z) (Test1:(0 >= y0)%Z), x0 = (x0 + y0)%Z.
Proof.
intros; omega.
Qed.


(* Why obligation from file , characters 608-636 *)
Lemma u11_po_1 : forall (r:Z) (Post1:r = 3%Z), (7 >= 0)%Z.
Proof.
intros; omega.
Qed.

(* Why obligation from file , characters 608-636 *)
Lemma u11_po_2 :
 forall (r:Z) (Post1:r = 3%Z) (Pre1:(7 >= 0)%Z) (r1:Z)
   (Post3:r1 = (r + 7)%Z), r1 = 10%Z.
Proof.
intros; omega.
Qed.


(* Why obligation from file , characters 933-947 *)
Lemma mult1_po_1 :
 forall (y x:Z) (Pre6:(x >= 0)%Z /\ (y >= 0)%Z) (z:Z) (Post4:z = y)
   (savex:Z) (Post3:savex = x) (x0:Z) (Post1:x0 = 0%Z)
   (Variant1 x1 z1:Z) (Pre5:Variant1 = z1)
   (I:(0 <= z1)%Z /\ x1 = (x * (y - z1))%Z) (Test2:(z1 > 0)%Z),
   (savex >= 0)%Z.
Proof.
intros; omega.
Qed.

(* Why obligation from file , characters 933-967 *)
Lemma mult1_po_2 :
 forall (y x:Z) (Pre6:(x >= 0)%Z /\ (y >= 0)%Z) (z:Z) (Post4:z = y)
   (savex:Z) (Post3:savex = x) (x0:Z) (Post1:x0 = 0%Z)
   (Variant1 x1 z1:Z) (Pre5:Variant1 = z1)
   (I:(0 <= z1)%Z /\ x1 = (x * (y - z1))%Z) (Test2:(z1 > 0)%Z)
   (Pre4:(savex >= 0)%Z) (x2:Z) (Post9:x2 = (x1 + savex)%Z) (z2:Z)
   (Post2:z2 = (z1 - 1)%Z),
   ((0 <= z2)%Z /\ x2 = (x * (y - z2))%Z) /\ Zwf 0 z2 z1.
Proof.
simpl; intros.
repeat split; unfold Zwf; try omega.
subst z2 x2 savex.
decompose [and] I.
subst x1.
ring.
Qed.

(* Why obligation from file , characters 868-904 *)
Lemma mult1_po_3 :
 forall (y x:Z) (Pre6:(x >= 0)%Z /\ (y >= 0)%Z) (z:Z) (Post4:z = y)
   (savex:Z) (Post3:savex = x) (x0:Z) (Post1:x0 = 0%Z),
   (0 <= z)%Z /\ x0 = (x * (y - z))%Z.
 Proof.
 intros.
subst z; split; [ omega | ring ]; assumption.
Qed.

(* Why obligation from file , characters 809-984 *)
Lemma mult1_po_4 :
 forall (y x:Z) (Pre6:(x >= 0)%Z /\ (y >= 0)%Z) (z:Z) (Post4:z = y)
   (savex:Z) (Post3:savex = x) (x0:Z) (Post1:x0 = 0%Z) (x1 z1:Z)
   (I:((0 <= z1)%Z /\ x1 = (x * (y - z1))%Z) /\ (z1 <= 0)%Z),
   x1 = (x * y)%Z.
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


(* Why obligation from file , characters 1042-1067 *)
Lemma u2_po_1 : forall (r:Z) (Post1:r = 4%Z), (r >= 0)%Z /\ (6 >= 0)%Z.
 Proof.
 intros; omega.
 Qed.

(* Why obligation from file , characters 1042-1067 *)
Lemma u2_po_2 :
 forall (r:Z) (Post1:r = 4%Z) (Pre1:(r >= 0)%Z /\ (6 >= 0)%Z) (r1:Z)
   (Post3:r1 = (r * 6)%Z), r1 = 24%Z.
 Proof.
 intros; omega.
 Qed.


