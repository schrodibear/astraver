
Require Import caduceus_why.


(*Why logic*) Definition sum : ((memory) Z) -> pointer -> Z -> Z -> Z.
Admitted.

(*Why axiom*) Lemma sum1 :
  (forall (intP:((memory) Z)),
   (forall (t:pointer), (forall (i:Z), (sum intP t i i) = 0))).
Admitted.

Admitted.

(* Why obligation from file "sum2.why", characters 515-544 *)
Lemma test1_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range t 0 n)),
  forall (i: Z),
  forall (Post6: i = (any_int tt)),
  forall (s: Z),
  forall (Post5: s = 0),
  forall (s1: Z),
  forall (Post1: s1 = s),
  forall (i1: Z),
  forall (Post2: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (s2: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ s2 = (sum intP t 0 i2)),
  forall (Test2: i2 < n),
  forall (aux_1: pointer),
  forall (Post13: aux_1 = (shift t i2)),
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

(* Why obligation from file "sum2.why", characters 515-544 *)
Lemma test1_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range t 0 n)),
  forall (i: Z),
  forall (Post6: i = (any_int tt)),
  forall (s: Z),
  forall (Post5: s = 0),
  forall (s1: Z),
  forall (Post1: s1 = s),
  forall (i1: Z),
  forall (Post2: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (s2: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ s2 = (sum intP t 0 i2)),
  forall (Test2: i2 < n),
  forall (aux_1: pointer),
  forall (Post13: aux_1 = (shift t i2)),
  forall (Pre2: ~(aux_1 = null) /\ 0 <= (offset aux_1) /\ (offset aux_1) <
                (length aux_1)),
  forall (result2: Z),
  forall (Post15: result2 = (acc intP aux_1)),
  (forall (i:Z),
   (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\ (s2 + result2) =
    (sum intP t 0 i)) /\ (Zwf 0 (n - i) (n - i2)))).
Proof.
intuition; subst; auto with *.
(* rewrite sum2... *)
Admitted.

(* Why obligation from file "sum2.why", characters 398-460 *)
Lemma test1_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range t 0 n)),
  forall (i: Z),
  forall (Post6: i = (any_int tt)),
  forall (s: Z),
  forall (Post5: s = 0),
  forall (s1: Z),
  forall (Post1: s1 = s),
  forall (i1: Z),
  forall (Post2: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ s1 = (sum intP t 0 i1).
Proof.
intuition.
assert (0<=n).
apply valid2 with t; auto.
omega.
subst.
(* rewrite sum1... *)
Admitted.

(* Why obligation from file "sum2.why", characters 588-590 *)
Lemma test1_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range t 0 n)),
  forall (i: Z),
  forall (Post6: i = (any_int tt)),
  forall (s: Z),
  forall (Post5: s = 0),
  forall (s1: Z),
  forall (Post1: s1 = s),
  forall (i1: Z),
  forall (Post2: i1 = 0),
  forall (i2: Z),
  forall (s2: Z),
  forall (Post4: ((0 <= i2 /\ i2 <= n) /\ s2 = (sum intP t 0 i2)) /\ i2 >= n),
  s2 = (sum intP t 0 n).
Proof.
intuition.
assert (i2=n).
omega.
subst; auto.
Save.

(* Why obligation from file "sum2.why", characters 1058-1081 *)
Lemma test2_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_range t 0 n)),
  forall (i: Z),
  forall (Post4: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre9: Variant1 = (n - i2)),
  forall (Pre8: (0 <= i2 /\ i2 <= n) /\ (sum intP0 t 0 n) =
                ((sum intP t 0 n) + i2)),
  forall (Test2: i2 < n),
  forall (caduceus1: pointer),
  forall (Post10: caduceus1 = (shift t i2)),
  ~(caduceus1 = null) /\ 0 <= (offset caduceus1) /\ (offset caduceus1) <
  (length caduceus1).
Proof.
Admitted.



(* Why obligation from file "sum2.why", characters 1042-1139 *)
Lemma test2_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_range t 0 n)),
  forall (i: Z),
  forall (Post4: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre9: Variant1 = (n - i2)),
  forall (Pre8: (0 <= i2 /\ i2 <= n) /\ (sum intP0 t 0 n) =
                ((sum intP t 0 n) + i2)),
  forall (Test2: i2 < n),
  forall (caduceus1: pointer),
  forall (Post10: caduceus1 = (shift t i2)),
  forall (Pre7: ~(caduceus1 = null) /\ 0 <= (offset caduceus1) /\
                (offset caduceus1) < (length caduceus1)),
  forall (caduceus2: Z),
  forall (Post12: caduceus2 = (acc intP0 caduceus1)),
  forall (Pre6: ~(caduceus1 = null) /\ 0 <= (offset caduceus1) /\
                (offset caduceus1) < (length caduceus1)),
  forall (intP1: ((memory) Z)),
  forall (Post14: intP1 = (upd intP0 caduceus1 (caduceus2 + 1))),
  (forall (i:Z),
   (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\ (sum intP1 t 0 n) =
    ((sum intP t 0 n) + i)) /\ (Zwf 0 (n - i) (n - i2)))).
Proof.
intuition; subst; auto with *.
(* TODO *)
Save.


(* Why obligation from file "sum2.why", characters 865-966 *)
Lemma test2_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_range t 0 n)),
  forall (i: Z),
  forall (Post4: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ (sum intP t 0 n) = ((sum intP t 0 n) + i1).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sum2.why", characters 793-1183 *)
Lemma test2_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_range t 0 n)),
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

