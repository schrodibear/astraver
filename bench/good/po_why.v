(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Import Omega.

(*Why logic*) Definition q : Z -> Prop.
Admitted.

(* Why obligation from file "good/po.mlw", characters 153-193 *)
Lemma p1_po_1 : 
  forall (x: Z),
  forall (Pre1: (q (x + 1))),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  (q x0).
 Proof.
 intros; rewrite Post1; assumption.
Qed.




(* Why obligation from file "good/po.mlw", characters 205-242 *)
Lemma p2_po_1 : 
  forall (Pre1: (q 7)),
  forall (x0: Z),
  forall (Post1: x0 = (3 + 4)),
  (q x0).
Proof.
intros; rewrite Post1; assumption.
Qed.




(* Why obligation from file "good/po.mlw", characters 254-305 *)
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




(* Why obligation from file "good/po.mlw", characters 317-359 *)
Lemma p4_po_1 : 
  forall (x0: Z),
  forall (Post1: x0 = 7),
  forall (x1: Z),
  forall (Post2: x1 = (2 * x0)),
  x1 = 14.
 Proof.
 intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 371-395 *)
Lemma p5_po_1 : 
  (3 + 4) = 7.
Proof.
omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 407-444 *)
Lemma p6_po_1 : 
  forall (a: Z),
  forall (Post2: a = 3),
  forall (result: Z),
  forall (Post1: result = (a + 4)),
  result = 7.
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 456-500 *)
Lemma p7_po_1 : 
  forall (aux_1: Z),
  forall (Post2: aux_1 = (4 + 4)),
  forall (result: Z),
  forall (Post1: result = (3 + aux_1)),
  result = 11.
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 573-595 *)
Lemma p8_po_1 : 
  forall (x: Z),
  forall (Pre1: (q (x + 1))),
  forall (x0: Z),
  forall (Post2: x0 = (x + 1)),
  forall (result0: Z),
  forall (Post3: result0 = x0),
  (forall (result:Z), (result = (3 + result0) -> (q x0) /\ result = (x + 4))).
Proof.
intuition; subst x0; assumption.
Qed.




(* Why obligation from file "good/po.mlw", characters 709-725 *)
Lemma p9_po_1 : 
  forall (x0: Z),
  forall (Post4: x0 = 2),
  forall (result0: Z),
  forall (Post5: result0 = 1),
  (forall (x:Z),
   (x = 1 ->
    (forall (result:Z),
     (result = 1 ->
      (forall (result1:Z),
       (result1 = (result + result0) -> result1 = 2 /\ x = 1)))))).
Proof.
intuition.
Qed.


(* Why obligation from file "good/po.mlw", characters 770-786 *)
Lemma p9a_po_1 : 
  forall (x0: Z),
  forall (Post2: x0 = 1),
  forall (result0: Z),
  forall (Post3: result0 = 1),
  (forall (result:Z), (result = (result0 + 1) -> result = 2 /\ x0 = 1)).
Proof.
intuition.
Qed.





(* Why obligation from file "good/po.mlw", characters 924-950 *)
Lemma p10_po_1 : 
  forall (result: Z),
  forall (Post1: result = 0),
  forall (result1: Z),
  forall (Post2: result1 = (0 + 1)),
  result1 = 1.
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 963-1003 *)
Lemma p11_po_1 : 
  forall (aux_2: Z),
  forall (Post2: aux_2 = (3 + 1)),
  forall (result: Z),
  forall (Post1: result = (0 + 1 + aux_2)),
  result = 5.
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 1017-1062 *)
Lemma p11a_po_1 : 
  forall (a: Z),
  forall (Post2: a = (1 + 1)),
  forall (result: Z),
  forall (Post1: result = (a + a)),
  result = 4.
Proof.
intros; omega.
Qed.





(* Why obligation from file "good/po.mlw", characters 1190-1221 *)
Lemma p12_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (result: unit),
  forall (Post1: result = tt),
  forall (x0: Z),
  forall (Post2: x0 = (x + 1)),
  x0 = 1.
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 1234-1287 *)
Lemma p13_po_1 : 
  forall (x: Z),
  forall (x0: Z),
  forall (Post3: x0 = (x + 1)),
  forall (x1: Z),
  forall (Post5: x1 = (x0 + 1)),
  x1 = (x + 2).
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 1301-1338 *)
Lemma p13a_po_1 : 
  forall (x: Z),
  forall (x0: Z),
  forall (Post3: x0 = (x + 1)),
  forall (x1: Z),
  forall (Post5: x1 = (x0 + 1)),
  x1 = (x + 2).
Proof.
intros; omega.
Qed.





(* Why obligation from file "good/po.mlw", characters 1487-1524 *)
Lemma p14_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (result: unit),
  forall (Post1: result = tt),
  forall (x0: Z),
  forall (result1: Z),
  forall (Post2: x0 = (x + 1) /\ result1 = x0),
  result1 = 1.
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 1576-1607 *)
Lemma p15_po_1 : 
  forall (t: (array Z)),
  forall (Pre3: (array_length t) = 10),
  0 <= 0 /\ 0 < (array_length t).
 (* p15_po_1 *)
Proof.
intros; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 1621-1657 *)
Lemma p16_po_1 : 
  forall (t: (array Z)),
  forall (Pre2: (array_length t) = 10),
  forall (aux_2: Z),
  forall (Post5: aux_2 = 1),
  forall (aux_1: Z),
  forall (Post4: aux_1 = 9),
  0 <= aux_1 /\ aux_1 < (array_length t).
 (* p16_po_1 *)
Proof.
intros; simpl; omega.
Qed.




(* Why obligation from file "good/po.mlw", characters 1717-1720 *)
Lemma p17_po_1 : 
  forall (t: (array Z)),
  forall (Pre3: (array_length t) = 10 /\ 0 <= (access t 0) /\ (access t 0) <
                10),
  forall (aux_2: Z),
  forall (Post5: aux_2 = 1),
  0 <= 0 /\ 0 < (array_length t).
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


(* Why obligation from file "good/po.mlw", characters 1671-1729 *)
Lemma p17_po_2 : 
  forall (t: (array Z)),
  forall (Pre3: (array_length t) = 10 /\ 0 <= (access t 0) /\ (access t 0) <
                10),
  forall (aux_2: Z),
  forall (Post5: aux_2 = 1),
  forall (Pre2: 0 <= 0 /\ 0 < (array_length t)),
  forall (aux_1: Z),
  forall (Post4: aux_1 = (access t 0)),
  0 <= aux_1 /\ aux_1 < (array_length t).
Proof.
intros; simpl; omega.
Qed.


(* Why obligation from file "good/po.mlw", characters 1774-1791 *)
Lemma p18_po_1 : 
  forall (t: (array Z)),
  forall (x: Z),
  forall (Pre2: (array_length t) = 10),
  forall (aux_2: Z),
  forall (Post6: aux_2 = x),
  forall (x0: Z),
  forall (Post4: x0 = 0),
  forall (result0: Z),
  forall (Post5: result0 = x0),
  (forall (t0:(array Z)), (t0 = (store t result0 aux_2) -> (access t0 0) = x)) /\
  0 <= result0 /\ result0 < (array_length t).
Proof.
intuition.
subst; AccessSame.
Qed.


