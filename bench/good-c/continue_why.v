(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.

(* Why obligation from file "good-c/continue.c", characters 130-139 *)
Lemma f1_po_1 : 
  forall (n: Z),
  forall (Post4: n = 10),
  forall (Variant1: Z),
  forall (n1: Z),
  forall (Pre3: Variant1 = n1),
  forall (Pre2: 0 <= n1),
  forall (Test4: n1 > 0),
  forall (Test3: n1 = 5),
  forall (n2: Z),
  forall (Post1: n2 = 0),
  0 <= n2 /\ (Zwf 0 n2 n1).
Proof.
intuition.
Qed.

(* Why obligation from file "good-c/continue.c", characters 109-141 *)
Lemma f1_po_2 : 
  forall (n: Z),
  forall (Post4: n = 10),
  forall (Variant1: Z),
  forall (n1: Z),
  forall (Pre3: Variant1 = n1),
  forall (Pre2: 0 <= n1),
  forall (Test4: n1 > 0),
  forall (Test2: n1 <> 5),
  (forall (n:Z), (n = (n1 - 1) -> 0 <= n /\ (Zwf 0 n n1))).
Proof.
intuition.
Qed.

(* Why obligation from file "good-c/continue.c", characters 84-90 *)
Lemma f1_po_3 : 
  forall (n: Z),
  forall (Post4: n = 10),
  0 <= n.
Proof.
intuition.
Qed.

(* Why obligation from file "good-c/continue.c", characters 164-165 *)
Lemma f1_po_4 : 
  forall (n: Z),
  forall (Post4: n = 10),
  forall (n1: Z),
  forall (Post3: 0 <= n1 /\ n1 <= 0),
  n1 = 0.
Proof.
intuition.
Qed.


(* Why obligation from file "good-c/continue.c", characters 312-321 *)
Lemma f2_po_1 : 
  forall (i: Z),
  forall (Post5: i = 17),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (Pre3: Variant1 = (10 - i2)),
  forall (Pre2: i2 <= 10),
  forall (Test4: i2 < 10),
  forall (Test3: i2 = 5),
  forall (i3: Z),
  forall (Post2: i3 = 6),
  i3 <= 10 /\ (Zwf 0 (10 - i3) (10 - i2)).
Proof.
intuition.
Qed.

(* Why obligation from file "good-c/continue.c", characters 291-323 *)
Lemma f2_po_2 : 
  forall (i: Z),
  forall (Post5: i = 17),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (Pre3: Variant1 = (10 - i2)),
  forall (Pre2: i2 <= 10),
  forall (Test4: i2 < 10),
  forall (Test2: i2 <> 5),
  (forall (i:Z), (i = (i2 + 1) -> i <= 10 /\ (Zwf 0 (10 - i) (10 - i2)))).
Proof.
intuition.
Qed.

(* Why obligation from file "good-c/continue.c", characters 260-267 *)
Lemma f2_po_3 : 
  forall (i: Z),
  forall (Post5: i = 17),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  i1 <= 10.
Proof.
intuition.
Qed.

(* Why obligation from file "good-c/continue.c", characters 337-338 *)
Lemma f2_po_4 : 
  forall (i: Z),
  forall (Post5: i = 17),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (i2: Z),
  forall (Post4: i2 <= 10 /\ i2 >= 10),
  i2 = 10.
Proof.
intuition.
Qed.


