(* Load Programs. *)(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.



(* Why obligation from file , characters 838-845 *)
Lemma p7_po_1 : forall (x0:Z) (Post1:x0 = 1%Z), x0 = 1%Z.
Proof.
intuition.
Qed.


(* Why obligation from file , characters 923-925 *)
Lemma p8_po_1 : forall (x0:Z) (Post1:x0 = 1%Z), x0 = 1%Z /\ x0 = 1%Z.
Proof.
intuition.
Qed.


(* Why obligation from file , characters 1020-1022 *)
Lemma p9_po_1 : forall (x0:Z) (Post1:x0 = 1%Z), x0 = 1%Z /\ x0 = 1%Z.
Proof.
intuition.
Qed.









(* Why obligation from file , characters 1372-1379 *)
Lemma p13_po_1 : forall x:Z, x = 2%Z -> x = 2%Z.
Proof.
intuition.
Qed.



(* Why obligation from file , characters 1557-1557 *)
Lemma p14_po_1 :
 forall (x:Z) (Test1:x <> 1%Z),
   (x = 2%Z -> x = 2%Z) /\
   (x <> 2%Z ->
    (x = 3%Z -> x = 3%Z) /\
    (x <> 3%Z -> x <> 1%Z /\ x <> 2%Z /\ x <> 3%Z)).
Proof.
intuition.
Qed.


