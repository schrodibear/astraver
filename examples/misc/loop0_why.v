(* Load Programs. *)
Require Import Why.
Require Import Omega.

(* Why obligation from file , characters 316-327 *)
Lemma p_po_1 :
 forall (x:Z) (Pre4:(x >= 0)%Z) (Variant1 x0:Z) (Pre3:Variant1 = x0)
   (Pre2:(0 <= x0)%Z /\ (x0 <= x)%Z) (Test2:(x0 > 0)%Z) (x1:Z)
   (Post1:x1 = (x0 - 1)%Z), ((0 <= x1)%Z /\ (x1 <= x)%Z) /\ Zwf 0 x1 x0.
 Proof.
 intuition.
 Qed.

(* Why obligation from file , characters 281-297 *)
Lemma p_po_2 : forall (x:Z) (Pre4:(x >= 0)%Z), (0 <= x)%Z /\ (x <= x)%Z.
Proof.
intuition.
Qed.

(* Why obligation from file , characters 227-348 *)
Lemma p_po_3 :
 forall (x:Z) (Pre4:(x >= 0)%Z) (x0:Z)
   (Post2:((0 <= x0)%Z /\ (x0 <= x)%Z) /\ (x0 <= 0)%Z), x0 = 0%Z.
Proof.
intuition.
Qed.
