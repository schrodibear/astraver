(* Load Programs. *)(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Import Omega.

Parameter q : Z -> Prop.

(* Why obligation from file "good/po.mlw", characters 153-194 *)
Lemma p1_po_1 : 
  forall (x: Z),
  forall (Pre1: (q (x + 1))),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  (q x0).
 Proof.
 intros; rewrite Post1; assumption.
Qed.




(* Why obligation from file "good/po.mlw", characters 205-243 *)
Lemma p2_po_1 : 
  forall (Pre1: (q 7)),
  forall (x0: Z),
  forall (Post1: x0 = (3 + 4)),
  (q x0).
Proof.
intros; rewrite Post1; assumption.
Qed.




(* Why obligation from file "good/po.mlw", characters 254-306 *)
Lemma p3_po_1 : 
  forall (x: Z),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  forall (x1: Z),
  forall (Post2: x1 = (x0 + 2)),
  x1 = (x + 3).
 Proof.
 intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 317-360 *)
Lemma p4_po_1 : 
  forall (x0: Z),
  forall (Post1: x0 = 7),
  forall (x1: Z),
  forall (Post2: x1 = (2 * x0)),
  x1 = 14.
 Proof.
 intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 371-396 *)
Lemma p5_po_1 : 
  (3 + 4) = 7.
Proof.
omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 424-429 *)
Lemma p6_po_1 : 
  forall (a: Z),
  forall (Post1: a = 3),
  (a + 4) = 7.
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 478-483 *)
Lemma p7_po_1 : 
  forall (a: Z),
  forall (Post1: a = 4),
  (3 + (a + a)) = 11.
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 592-594 *)
Lemma p8_po_1 : 
  forall (x: Z),
  forall (Pre1: (q (x + 1))),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  (q x0) /\ (3 + x0) = (x + 4).
Proof.
intuition; rewrite Post1; assumption.
Qed.




(* Why obligation from file "good/po.mlw", characters 723-724 *)
Lemma p9_po_1 : 
  forall (x0: Z),
  forall (Post3: x0 = 2),
  (forall (x:Z), (x = 1 -> (1 + 1) = 2 /\ x = 1)).
Proof.
intuition.
Qed.


(* Why obligation from file "good/po.mlw", characters 784-785 *)
Lemma p9a_po_1 : 
  forall (x0: Z),
  forall (Post2: x0 = 1),
  (1 + 1) = 2 /\ x0 = 1.
Proof.
intuition.
Qed.




(*Why*) Parameter fsucc :
  forall (x: Z), (sig_1 Z (fun (result: Z)  => (result = (x + 1)))).

(* Why obligation from file "good/po.mlw", characters 924-951 *)
Lemma p10_po_1 : 
  forall (result1: Z),
  forall (Post1: result1 = (0 + 1)),
  result1 = 1.
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 963-1004 *)
Lemma p11_po_1 : 
  forall (aux_2: Z),
  forall (Post1: aux_2 = (3 + 1)),
  forall (aux_1: Z),
  forall (Post4: aux_1 = (0 + 1)),
  (aux_1 + aux_2) = 5.
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 1042-1047 *)
Lemma p11a_po_1 : 
  forall (a: Z),
  forall (Post1: a = (1 + 1)),
  (a + a) = 4.
Proof.
intros; omega.
Qed.




(*Why*) Parameter incrx :
  forall (_: unit), forall (x: Z),
  (sig_2 Z unit (fun (x0: Z) (result: unit)  => (x0 = (x + 1)))).

(* Why obligation from file "good/po.mlw", characters 1190-1222 *)
Lemma p12_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  x0 = 1.
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 1234-1288 *)
Lemma p13_po_1 : 
  forall (x: Z),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  forall (x1: Z),
  forall (Post3: x1 = (x0 + 1)),
  x1 = (x + 2).
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 1301-1339 *)
Lemma p13a_po_1 : 
  forall (x: Z),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  forall (x1: Z),
  forall (Post3: x1 = (x0 + 1)),
  x1 = (x + 2).
Proof.
intros; omega.
Qed.




(*Why*) Parameter incrx2 :
  forall (_: unit), forall (x: Z),
  (sig_2 Z Z (fun (x0: Z) (result: Z)  => (x0 = (x + 1) /\ result = x0))).

(* Why obligation from file "good/po.mlw", characters 1487-1525 *)
Lemma p14_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (x0: Z),
  forall (result1: Z),
  forall (Post1: x0 = (x + 1) /\ result1 = x0),
  result1 = 1.
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 1576-1608 *)
Lemma p15_po_1 : 
  forall (t: (array Z)),
  forall (Pre2: (array_length t) = 10),
  0 <= 0 /\ 0 < (array_length t).
 (* p15_po_1 *)
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 1621-1658 *)
Lemma p16_po_1 : 
  forall (t: (array Z)),
  forall (Pre2: (array_length t) = 10),
  0 <= 9 /\ 9 < (array_length t).
 (* p16_po_1 *)
Proof.
intros; simpl; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 1671-1730 *)
Lemma p17_po_1 : 
  forall (t: (array Z)),
  forall (Pre3: (array_length t) = 10 /\ 0 <= (access t 0) /\ (access t 0) <
                10),
  0 <= (access t 0) /\ (access t 0) < (array_length t).
 (* p17_po_1 *)
Proof.
intros; omega.
Qed.


(* 
 Local Variables:
 mode: coq 
  coq-prog-name: 
 End:
*)


(* Why obligation from file "good/po.mlw", characters 1717-1721 *)
Lemma p17_po_2 : 
  forall (t: (array Z)),
  forall (Pre3: (array_length t) = 10 /\ 0 <= (access t 0) /\ (access t 0) <
                10),
  forall (Pre2: 0 <= (access t 0) /\ (access t 0) < (array_length t)),
  0 <= 0 /\ 0 < (array_length t).
Proof.
intros; simpl; omega.
Qed.


(* Why obligation from file "good/po.mlw", characters 1788-1790 *)
Lemma p18_po_1 : 
  forall (t: (array Z)),
  forall (x: Z),
  forall (Pre2: (array_length t) = 10),
  forall (aux_2: Z),
  forall (Post2: aux_2 = x),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  (access (store t x0 aux_2) 0) = x /\ 0 <= x0 /\ x0 < (array_length t).
Proof.
intuition.
subst x0; AccessSame.
Qed.


