
Require Import caduceus_why.


(*Why logic*) Definition sum : ((memory) Z) -> pointer -> Z -> Z -> Z.
Admitted.

(*Why axiom*) Lemma sum1 :
  (forall (intP:((memory) Z)),
   (forall (t:pointer), (forall (i:Z), (sum intP t i i) = 0))).
Admitted.

(*Why axiom*) Lemma sum2 :
  (forall (intP:((memory) Z)),
   (forall (t:pointer),
    (forall (i:Z),
     (forall (j:Z), (sum intP t i (j + 1)) =
      ((sum intP t i j) + (acc intP (shift t j))))))).
Admitted.

(* Why obligation from file "sum2.why", characters 709-738 *)
Lemma test1_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid t 0 n)),
  forall (i: Z),
  forall (Post5: i = (any_int tt)),
  forall (s: Z),
  forall (Post4: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (s1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ s1 = (sum intP t 0 i2)),
  forall (Test2: i2 < n),
  forall (aux_1: pointer),
  forall (Post11: aux_1 = (shift t i2)),
  ~(aux_1 = null) /\ 0 <= (offset aux_1) /\ (offset aux_1) < (length aux_1).
Proof.
intuition.
apply shift_not_null with (p:=t) (i:=i2).
apply valid_not_null with (i:=0) (j:=n).
auto.
subst; auto.
subst aux_1.
rewrite offset_shift.
assert (0 <= offset t + 0).
apply valid1 with (p:=t) (i:=0) (j:=n). 
assumption.
omega.
subst aux_1.
rewrite offset_shift.
rewrite length_shift.
assert (offset t + n <= length t).
apply valid3 with (i:=0).
assumption.
omega.
Qed.

(* Why obligation from file "sum2.why", characters 709-738 *)
Lemma test1_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid t 0 n)),
  forall (i: Z),
  forall (Post5: i = (any_int tt)),
  forall (s: Z),
  forall (Post4: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (s1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ s1 = (sum intP t 0 i2)),
  forall (Test2: i2 < n),
  forall (aux_1: pointer),
  forall (Post11: aux_1 = (shift t i2)),
  forall (Pre2: ~(aux_1 = null) /\ 0 <= (offset aux_1) /\ (offset aux_1) <
                (length aux_1)),
  forall (result1: Z),
  forall (Post13: result1 = (acc intP aux_1)),
  (forall (i:Z),
   (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\ (s1 + result1) =
    (sum intP t 0 i)) /\ (Zwf 0 (n - i) (n - i2)))).
Proof.
intuition; subst; auto with *.
(* rewrite sum2... *)
Admitted.

(* Why obligation from file "sum2.why", characters 594-656 *)
Lemma test1_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid t 0 n)),
  forall (i: Z),
  forall (Post5: i = (any_int tt)),
  forall (s: Z),
  forall (Post4: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ s = (sum intP t 0 i1).
Proof.
intuition.
assert (0<=n).
apply valid2 with t; auto.
omega.
subst.
(* rewrite sum1... *)
Admitted.

(* Why obligation from file "sum2.why", characters 779-781 *)
Lemma test1_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid t 0 n)),
  forall (i: Z),
  forall (Post5: i = (any_int tt)),
  forall (s: Z),
  forall (Post4: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (i2: Z),
  forall (s1: Z),
  forall (Post3: ((0 <= i2 /\ i2 <= n) /\ s1 = (sum intP t 0 i2)) /\ i2 >= n),
  s1 = (sum intP t 0 n).
Proof.
intuition.
assert (i2=n).
omega.
subst; auto.
Save.

(* Why obligation from file "sum2.why", characters 1255-1284 *)
Lemma test2_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre8: (valid t 0 n)),
  forall (i: Z),
  forall (Post4: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre7: Variant1 = (n - i2)),
  forall (Pre6: (0 <= i2 /\ i2 <= n) /\ (sum intP0 t 0 n) =
                ((sum intP t 0 n) + i2)),
  forall (Test2: i2 < n),
  forall (caduceus1: pointer),
  forall (Post10: caduceus1 = (shift t i2)),
  forall (aux_1: pointer),
  forall (Post12: aux_1 = (shift t i2)),
  ~(aux_1 = null) /\ 0 <= (offset aux_1) /\ (offset aux_1) < (length aux_1).
Proof.
Admitted.



(* Why obligation from file "sum2.why", characters 1255-1284 *)
Lemma test2_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre8: (valid t 0 n)),
  forall (i: Z),
  forall (Post4: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre7: Variant1 = (n - i2)),
  forall (Pre6: (0 <= i2 /\ i2 <= n) /\ (sum intP0 t 0 n) =
                ((sum intP t 0 n) + i2)),
  forall (Test2: i2 < n),
  forall (caduceus1: pointer),
  forall (Post10: caduceus1 = (shift t i2)),
  forall (aux_1: pointer),
  forall (Post12: aux_1 = (shift t i2)),
  forall (Pre2: ~(aux_1 = null) /\ 0 <= (offset aux_1) /\ (offset aux_1) <
                (length aux_1)),
  forall (result1: Z),
  forall (Post14: result1 = (acc intP0 aux_1)),
  (forall (intP1:((memory) Z)),
   (intP1 = (upd intP0 caduceus1 (result1 + 1)) ->
    (forall (i:Z),
     (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\ (sum intP1 t 0 n) =
      ((sum intP t 0 n) + i)) /\ (Zwf 0 (n - i) (n - i2)))))) /\
  ~(caduceus1 = null) /\ 0 <= (offset caduceus1) /\ (offset caduceus1) <
  (length caduceus1).
Proof.
intuition; subst; auto with *.
(* TODO *)
Save.


(* Why obligation from file "sum2.why", characters 1043-1144 *)
Lemma test2_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre8: (valid t 0 n)),
  forall (i: Z),
  forall (Post4: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ (sum intP t 0 n) = ((sum intP t 0 n) + i1).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sum2.why", characters 971-1333 *)
Lemma test2_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre8: (valid t 0 n)),
  forall (i: Z),
  forall (Post4: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Post3: ((0 <= i2 /\ i2 <= n) /\ (sum intP0 t 0 n) =
                 ((sum intP t 0 n) + i2)) /\ i2 >= n),
  (sum intP0 t 0 n) = ((sum intP t 0 n) + n).
Proof.
(* FILL PROOF HERE *)
Save.

