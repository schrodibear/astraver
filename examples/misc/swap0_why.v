(* Load Programs. *)Require Import Why.
Require Import Omega.

(* Why obligation from file , characters 149-174 *)
Lemma swap1_po_1 :
 forall (x y t:Z) (Post3:t = x) (x0:Z) (Post1:x0 = y) (y0:Z)
   (Post2:y0 = t), x0 = y /\ y0 = x.
Proof.
intuition.
Qed.


(* Why obligation from file , characters 316-358 *)
Lemma swap2_po_1 :
 forall (x y t:Z) (Post3:t = x) (x0:Z) (Post1:x0 = y) (y0:Z)
   (Post2:y0 = t), x0 = y /\ y0 = x.
Proof.
intuition.
Qed.


(* Why obligation from file , characters 509-534 *)
Lemma swap3_po_1 :
 forall (a b t:Z) (Post3:t = a) (a0:Z) (Post1:a0 = b) (b0:Z)
   (Post2:b0 = t), a0 = b /\ b0 = a.
Proof.
intuition.
Qed.


(* Why obligation from file , characters 654-678 *)
Lemma test_swap3_po_1 :
 forall (c:Z) (Post2:c = 1%Z) (d:Z) (Post1:d = 2%Z) (c1 d1:Z)
   (Post4:c1 = d /\ d1 = c), d1 = 1%Z.
 (* test_swap3_po_1 *)
Proof.
intuition.
Qed.



(* Why obligation from file , characters 790-826 *)
Lemma call_swap3_y_x_po_1 :
 forall (x y y0 x0:Z) (Post1:y0 = x /\ x0 = y), x0 = y /\ y0 = x.
 (* call_swap3_y_x_po_1 *)
Proof.
intuition.
Qed.


(* Why obligation from file , characters 945-1014 *)
Lemma swap4_po_1 :
 forall (a b tmp0:Z) (Post1:tmp0 = a) (a0:Z) (Post2:a0 = b) (b0:Z)
   (Post3:b0 = tmp0), a0 = b /\ b0 = a.
Proof.
intuition.
Qed.


(* Why obligation from file , characters 1109-1133 *)
Lemma test_swap4_po_1 :
 forall (c:Z) (Post2:c = 1%Z) (d:Z) (Post1:d = 2%Z) (c1 d1:Z)
   (Post4:c1 = d /\ d1 = c), d1 = 1%Z.
 (* test_swap4_po_1 *)
Proof.
intuition.
Qed.


(* Why obligation from file , characters 1187-1218 *)
Lemma call_swap4_x_y_po_1 :
 forall (x y:Z) (Pre1:x = 3%Z) (x0 y0:Z) (Post1:x0 = y /\ y0 = x),
   y0 = 3%Z.
Proof.
intuition.
Qed.


(* Why obligation from file , characters 1240-1271 *)
Lemma call_swap4_y_x_po_1 :
 forall (x y:Z) (Pre1:x = 3%Z) (y0 x0:Z) (Post1:y0 = x /\ x0 = y),
   y0 = 3%Z.
Proof.
intuition.
Qed.


