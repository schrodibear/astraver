(* Load Programs. *)
Require Import Why.
Require Import Omega.

(* Why obligation from file "loops.mlw", characters 156-167 *)
Lemma loop1_po_1 : 
  forall (i: Z),
  forall (Pre6: i <= 10),
  forall (Variant1: Z),
  forall (i0: Z),
  forall (Pre5: Variant1 = (10 - i0)),
  forall (Pre4: i0 <= 10),
  forall (Test2: i0 < 10),
  forall (Pre3: i0 <= 10),
  forall (i1: Z),
  forall (Post1: i1 = (i0 + 1)),
  i1 <= 10 /\ (Zwf 0 (10 - i1) (10 - i0)).
Proof.
unfold Zwf; intros; omega.
Qed.

(* Why obligation from file "loops.mlw", characters 82-187 *)
Lemma loop1_po_2 : 
  forall (i: Z),
  forall (Pre6: i <= 10),
  forall (Variant1: Z),
  forall (i0: Z),
  forall (Pre5: Variant1 = (10 - i0)),
  forall (Pre4: i0 <= 10),
  forall (Test1: i0 >= 10),
  forall (Pre2: i0 <= 10),
  i0 = 10.
Proof.
intros; omega.
Qed.







(* Why obligation from file "loops.mlw", characters 414-425 *)
Lemma loop2_po_1 : 
  forall (x: Z),
  forall (Pre4: x <= 10),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (Pre3: Variant1 = (10 - x0)),
  forall (Pre2: x0 <= 10),
  forall (Test2: x0 < 10),
  forall (x1: Z),
  forall (Post1: x1 = (x0 + 1)),
  x1 <= 10 /\ (Zwf 0 (10 - x1) (10 - x0)).
Proof.
unfold Zwf; intros; omega.
Qed.

(* Why obligation from file "loops.mlw", characters 354-445 *)
Lemma loop2_po_2 : 
  forall (x: Z),
  forall (Pre4: x <= 10),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (Pre3: Variant1 = (10 - x0)),
  forall (Pre2: x0 <= 10),
  forall (Test1: x0 >= 10),
  x0 = 10.
Proof.
intros; intuition.
Qed.

(* Why obligation from file "loops.mlw", characters 474-487 *)
Lemma loop2_po_3 : 
  forall (x: Z),
  forall (Pre4: x <= 10),
  forall (x0: Z),
  forall (Post4: x0 = 10),
  forall (Test4: x0 > 0),
  forall (x1: Z),
  forall (Post11: x1 = (Zopp x0)),
  x1 = (Zopp 10).
Proof.
simpl; intros; omega.
Qed.

(* Why obligation from file "loops.mlw", characters 487-487 *)
Lemma loop2_po_4 : 
  forall (x: Z),
  forall (Pre4: x <= 10),
  forall (x0: Z),
  forall (Post4: x0 = 10),
  forall (Test3: x0 <= 0),
  x0 = (Zopp 10).
Proof.
intros; omega.
Qed.




