(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Import Omega.

(*Why logic*) Definition q : Z -> Prop.
Admitted.

(* Why obligation from file "po.mlw", characters 170-181 *)
Lemma p1_po_1 : 
  forall (x: Z),
  forall (Pre1: (q (x + 1))),
  forall (result: Z),
  forall (Post1: result = (x + 1)),
  (q result).
 Proof.
 intros; rewrite Post1; assumption.
Qed.




(* Why obligation from file "po.mlw", characters 220-230 *)
Lemma p2_po_1 : 
  forall (Pre1: (q 7)),
  forall (result: Z),
  forall (Post1: result = (3 + 4)),
  (q result).
Proof.
intros; rewrite Post1; assumption.
Qed.




(* Why obligation from file "po.mlw", characters 263-274 *)
Lemma p3_po_1 : 
  forall (x: Z),
  forall (result: Z),
  forall (Post1: result = (x + 1)),
  (forall (result0:Z), (result0 = (result + 2) -> result0 = (x + 3))).
 Proof.
 intros; omega.
Qed.




(* Why obligation from file "po.mlw", characters 326-332 *)
Lemma p4_po_1 : 
  forall (result: Z),
  forall (Post1: result = 7),
  (forall (result0:Z), (result0 = (2 * result) -> result0 = 14)).
 Proof.
 intros; omega.
Qed.




(* Why obligation from file "po.mlw", characters 371-396 *)
Lemma p5_po_1 : 
  (3 + 4) = 7.
Proof.
omega.
Qed.




(* Why obligation from file "po.mlw", characters 407-445 *)
Lemma p6_po_1 : 
  forall (a: Z),
  forall (Post2: a = 3),
  forall (result: Z),
  forall (Post1: result = (a + 4)),
  result = 7.
Proof.
intros; omega.
Qed.




(* Why obligation from file "po.mlw", characters 456-501 *)
Lemma p7_po_1 : 
  forall (aux_1: Z),
  forall (Post2: aux_1 = (4 + 4)),
  forall (result: Z),
  forall (Post1: result = (3 + aux_1)),
  result = 11.
Proof.
intros; omega.
Qed.




(* Why obligation from file "po.mlw", characters 579-590 *)
Lemma p8_po_1 : 
  forall (x: Z),
  forall (Pre1: (q (x + 1))),
  forall (result: Z),
  forall (Post2: result = (x + 1)),
  (forall (result0:Z),
   (result0 = result ->
    (forall (result1:Z),
     (result1 = (3 + result0) -> (q result) /\ result1 = (x + 4))))).
Proof.
intuition; rewrite Post1; assumption.
Qed.




(* Why obligation from file "po.mlw", characters 715-721 *)
Lemma p9_po_1 : 
  forall (result: Z),
  forall (Post4: result = 2),
  (forall (result:Z),
   (result = 1 ->
    (forall (result0:Z),
     (result0 = 1 ->
      (forall (result1:Z),
       (result1 = 1 ->
        (forall (result2:Z),
         (result2 = (result1 + result) -> result2 = 2 /\ result0 = 1)))))))).
Proof.
intuition.
Qed.


(* Why obligation from file "po.mlw", characters 776-782 *)
Lemma p9a_po_1 : 
  forall (result: Z),
  forall (Post2: result = 1),
  (forall (result0:Z),
   (result0 = 1 ->
    (forall (result1:Z),
     (result1 = (result0 + 1) -> result1 = 2 /\ result = 1)))).
Proof.
intuition.
Qed.





(* Why obligation from file "po.mlw", characters 924-951 *)
Lemma p10_po_1 : 
  forall (result: Z),
  forall (Post1: result = 0),
  forall (result1: Z),
  forall (Post2: result1 = (0 + 1)),
  result1 = 1.
Proof.
intros; omega.
Qed.




(* Why obligation from file "po.mlw", characters 963-1004 *)
Lemma p11_po_1 : 
  forall (aux_2: Z),
  forall (Post2: aux_2 = (3 + 1)),
  forall (result: Z),
  forall (Post1: (exists aux_1:Z, aux_1 = (0 + 1) /\ result = (aux_1 + aux_2))),
  result = 5.
Proof.
intros; omega.
Qed.




(* Why obligation from file "po.mlw", characters 1017-1063 *)
Lemma p11a_po_1 : 
  forall (a: Z),
  forall (Post2: a = (1 + 1)),
  forall (result: Z),
  forall (Post1: result = (a + a)),
  result = 4.
Proof.
intros; omega.
Qed.





(* Why obligation from file "po.mlw", characters 1190-1222 *)
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




(* Why obligation from file "po.mlw", characters 1234-1288 *)
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




(* Why obligation from file "po.mlw", characters 1301-1339 *)
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





(* Why obligation from file "po.mlw", characters 1487-1525 *)
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




(* Why obligation from file "po.mlw", characters 1576-1608 *)
Lemma p15_po_1 : 
  forall (t: (array Z)),
  forall (Pre3: (array_length t) = 10),
  0 <= 0 /\ 0 < (array_length t).
 (* p15_po_1 *)
Proof.
intros; omega.
Qed.




(* Why obligation from file "po.mlw", characters 1621-1658 *)
Lemma p16_po_1 : 
  forall (t: (array Z)),
  forall (Pre2: (array_length t) = 10),
  forall (aux_2: Z),
  forall (Post4: aux_2 = 1),
  forall (aux_1: Z),
  forall (Post3: aux_1 = 9),
  0 <= aux_1 /\ aux_1 < (array_length t).
 (* p16_po_1 *)
Proof.
intros; simpl; omega.
Qed.




(* Why obligation from file "po.mlw", characters 1717-1721 *)
Lemma p17_po_1 : 
  forall (t: (array Z)),
  forall (Pre3: (array_length t) = 10 /\ 0 <= (access t 0) /\ (access t 0) <
                10),
  forall (aux_2: Z),
  forall (Post4: aux_2 = 1),
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


(* Why obligation from file "po.mlw", characters 1671-1730 *)
Lemma p17_po_2 : 
  forall (t: (array Z)),
  forall (Pre3: (array_length t) = 10 /\ 0 <= (access t 0) /\ (access t 0) <
                10),
  forall (aux_2: Z),
  forall (Post4: aux_2 = 1),
  forall (Pre2: 0 <= 0 /\ 0 < (array_length t)),
  forall (aux_1: Z),
  forall (Post3: aux_1 = (access t 0)),
  0 <= aux_1 /\ aux_1 < (array_length t).
Proof.
intros; simpl; omega.
Qed.


(* Why obligation from file "po.mlw", characters 1780-1786 *)
Lemma p18_po_1 : 
  forall (t: (array Z)),
  forall (x: Z),
  forall (Pre2: (array_length t) = 10),
  forall (aux_2: Z),
  forall (Post5: aux_2 = x),
  forall (result: Z),
  forall (Post3: result = 0),
  (forall (result0:Z),
   (result0 = result -> (access (store t result0 aux_2) 0) = x /\ 0 <=
    result0 /\ result0 < (array_length t))).
Proof.
intuition.
subst x0; AccessSame.
Qed.


(* Why obligation from file "po.mlw", characters 1746-1816 *)
Lemma p18_po_2 : 
  forall (t: (array Z)),
  forall (x: Z),
  forall (Pre2: (array_length t) = 10),
  forall (aux_2: Z),
  forall (Post5: aux_2 = x),
  forall (aux_1: Z),
  forall (Pre1: 0 <= aux_1 /\ aux_1 < (array_length t)),
  forall (result: Z),
  forall (Post1: result = aux_2),
  forall (result0: Z),
  forall (Post2: result0 = aux_1),
  (access (store t result0 result) 0) = x.
Proof.
(* FILL PROOF HERE *)
Save.

