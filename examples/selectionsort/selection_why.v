(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Import Omega.


(* Why obligation from file "selection.mlw", characters 804-809 *)
Lemma selection_po_1 : 
  forall (t: (array Z)),
  forall (Pre19: (array_length t) >= 1),
  forall (i: Z),
  forall (Post11: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Pre18: Variant1 = ((array_length t0) - i1)),
  forall (Pre17: (0 <= i1 /\ i1 <= ((array_length t0) - 1)) /\
                 (sorted_array t0 0 (i1 - 1)) /\ (permut t0 t) /\
                 (forall (k:Z),
                  (0 <= k /\ k < i1 ->
                   (forall (l:Z),
                    (i1 <= l /\ l < (array_length t0) -> (access t0 k) <=
                     (access t0 l)))))),
  forall (Test6: i1 < ((array_length t0) - 1)),
  forall (min: Z),
  forall (Post8: min = i1),
  forall (j: Z),
  forall (Post7: j = (i1 + 1)),
  forall (Variant3: Z),
  forall (j1: Z),
  forall (min1: Z),
  forall (Pre12: Variant3 = ((array_length t0) - j1)),
  forall (Pre11: ((i1 + 1) <= j1 /\ j1 <= (array_length t0)) /\ (i1 <=
                 min1 /\ min1 < (array_length t0)) /\
                 (forall (k:Z),
                  (i1 <= k /\ k < j1 -> (access t0 min1) <= (access t0 k)))),
  forall (Test5: j1 < (array_length t0)),
  0 <= j1 /\ j1 < (array_length t0).
Proof.
auto with *.
Qed.

(* Why obligation from file "selection.mlw", characters 812-819 *)
Lemma selection_po_2 : 
  forall (t: (array Z)),
  forall (Pre19: (array_length t) >= 1),
  forall (i: Z),
  forall (Post11: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Pre18: Variant1 = ((array_length t0) - i1)),
  forall (Pre17: (0 <= i1 /\ i1 <= ((array_length t0) - 1)) /\
                 (sorted_array t0 0 (i1 - 1)) /\ (permut t0 t) /\
                 (forall (k:Z),
                  (0 <= k /\ k < i1 ->
                   (forall (l:Z),
                    (i1 <= l /\ l < (array_length t0) -> (access t0 k) <=
                     (access t0 l)))))),
  forall (Test6: i1 < ((array_length t0) - 1)),
  forall (min: Z),
  forall (Post8: min = i1),
  forall (j: Z),
  forall (Post7: j = (i1 + 1)),
  forall (Variant3: Z),
  forall (j1: Z),
  forall (min1: Z),
  forall (Pre12: Variant3 = ((array_length t0) - j1)),
  forall (Pre11: ((i1 + 1) <= j1 /\ j1 <= (array_length t0)) /\ (i1 <=
                 min1 /\ min1 < (array_length t0)) /\
                 (forall (k:Z),
                  (i1 <= k /\ k < j1 -> (access t0 min1) <= (access t0 k)))),
  forall (Test5: j1 < (array_length t0)),
  forall (Pre9: 0 <= j1 /\ j1 < (array_length t0)),
  0 <= min1 /\ min1 < (array_length t0).
Proof.
intuition.
Qed.

(* Why obligation from file "selection.mlw", characters 825-834 *)
Lemma selection_po_3 : 
  forall (t: (array Z)),
  forall (Pre19: (array_length t) >= 1),
  forall (i: Z),
  forall (Post11: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Pre18: Variant1 = ((array_length t0) - i1)),
  forall (Pre17: (0 <= i1 /\ i1 <= ((array_length t0) - 1)) /\
                 (sorted_array t0 0 (i1 - 1)) /\ (permut t0 t) /\
                 (forall (k:Z),
                  (0 <= k /\ k < i1 ->
                   (forall (l:Z),
                    (i1 <= l /\ l < (array_length t0) -> (access t0 k) <=
                     (access t0 l)))))),
  forall (Test6: i1 < ((array_length t0) - 1)),
  forall (min: Z),
  forall (Post8: min = i1),
  forall (j: Z),
  forall (Post7: j = (i1 + 1)),
  forall (Variant3: Z),
  forall (j1: Z),
  forall (min1: Z),
  forall (Pre12: Variant3 = ((array_length t0) - j1)),
  forall (Pre11: ((i1 + 1) <= j1 /\ j1 <= (array_length t0)) /\ (i1 <=
                 min1 /\ min1 < (array_length t0)) /\
                 (forall (k:Z),
                  (i1 <= k /\ k < j1 -> (access t0 min1) <= (access t0 k)))),
  forall (Test5: j1 < (array_length t0)),
  forall (Pre9: 0 <= j1 /\ j1 < (array_length t0)),
  forall (Pre10: 0 <= min1 /\ min1 < (array_length t0)),
  forall (Test4: (access t0 j1) < (access t0 min1)),
  forall (min2: Z),
  forall (Post1: min2 = j1),
  (forall (j:Z),
   (j = (j1 + 1) -> (((i1 + 1) <= j /\ j <= (array_length t0)) /\ (i1 <=
    min2 /\ min2 < (array_length t0)) /\
    (forall (k:Z), (i1 <= k /\ k < j -> (access t0 min2) <= (access t0 k)))) /\
    (Zwf 0 ((array_length t0) - j) ((array_length t0) - j1)))).
Proof.
intuition.
assert h: (k < j1)%Z \/ k = j1.
 omega.
 intuition.
apply Zle_trans with (access t0 min1).
subst min2; omega.
apply H12; omega.
subst min2 k; omega.
Qed.

(* Why obligation from file "selection.mlw", characters 834-834 *)
Lemma selection_po_4 : 
  forall (t: (array Z)),
  forall (Pre19: (array_length t) >= 1),
  forall (i: Z),
  forall (Post11: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Pre18: Variant1 = ((array_length t0) - i1)),
  forall (Pre17: (0 <= i1 /\ i1 <= ((array_length t0) - 1)) /\
                 (sorted_array t0 0 (i1 - 1)) /\ (permut t0 t) /\
                 (forall (k:Z),
                  (0 <= k /\ k < i1 ->
                   (forall (l:Z),
                    (i1 <= l /\ l < (array_length t0) -> (access t0 k) <=
                     (access t0 l)))))),
  forall (Test6: i1 < ((array_length t0) - 1)),
  forall (min: Z),
  forall (Post8: min = i1),
  forall (j: Z),
  forall (Post7: j = (i1 + 1)),
  forall (Variant3: Z),
  forall (j1: Z),
  forall (min1: Z),
  forall (Pre12: Variant3 = ((array_length t0) - j1)),
  forall (Pre11: ((i1 + 1) <= j1 /\ j1 <= (array_length t0)) /\ (i1 <=
                 min1 /\ min1 < (array_length t0)) /\
                 (forall (k:Z),
                  (i1 <= k /\ k < j1 -> (access t0 min1) <= (access t0 k)))),
  forall (Test5: j1 < (array_length t0)),
  forall (Pre9: 0 <= j1 /\ j1 < (array_length t0)),
  forall (Pre10: 0 <= min1 /\ min1 < (array_length t0)),
  forall (Test3: (access t0 j1) >= (access t0 min1)),
  (forall (j:Z),
   (j = (j1 + 1) -> (((i1 + 1) <= j /\ j <= (array_length t0)) /\ (i1 <=
    min1 /\ min1 < (array_length t0)) /\
    (forall (k:Z), (i1 <= k /\ k < j -> (access t0 min1) <= (access t0 k)))) /\
    (Zwf 0 ((array_length t0) - j) ((array_length t0) - j1)))).
Proof.
intuition.
assert h: (k < j1)%Z \/ k = j1.
 omega.
 intuition.
subst k; omega.
Qed.

(* Why obligation from file "selection.mlw", characters 619-755 *)
Lemma selection_po_5 : 
  forall (t: (array Z)),
  forall (Pre19: (array_length t) >= 1),
  forall (i: Z),
  forall (Post11: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Pre18: Variant1 = ((array_length t0) - i1)),
  forall (Pre17: (0 <= i1 /\ i1 <= ((array_length t0) - 1)) /\
                 (sorted_array t0 0 (i1 - 1)) /\ (permut t0 t) /\
                 (forall (k:Z),
                  (0 <= k /\ k < i1 ->
                   (forall (l:Z),
                    (i1 <= l /\ l < (array_length t0) -> (access t0 k) <=
                     (access t0 l)))))),
  forall (Test6: i1 < ((array_length t0) - 1)),
  forall (min: Z),
  forall (Post8: min = i1),
  forall (j: Z),
  forall (Post7: j = (i1 + 1)),
  ((i1 + 1) <= j /\ j <= (array_length t0)) /\ (i1 <= min /\ min <
  (array_length t0)) /\
  (forall (k:Z), (i1 <= k /\ k < j -> (access t0 min) <= (access t0 k))).
Proof.
intuition.
assert h: k = i1.
 omega.
subst min k; omega.
Qed.

(* Why obligation from file "selection.mlw", characters 898-905 *)
Lemma selection_po_6 : 
  forall (t: (array Z)),
  forall (Pre19: (array_length t) >= 1),
  forall (i: Z),
  forall (Post11: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Pre18: Variant1 = ((array_length t0) - i1)),
  forall (Pre17: (0 <= i1 /\ i1 <= ((array_length t0) - 1)) /\
                 (sorted_array t0 0 (i1 - 1)) /\ (permut t0 t) /\
                 (forall (k:Z),
                  (0 <= k /\ k < i1 ->
                   (forall (l:Z),
                    (i1 <= l /\ l < (array_length t0) -> (access t0 k) <=
                     (access t0 l)))))),
  forall (Test6: i1 < ((array_length t0) - 1)),
  forall (min: Z),
  forall (Post8: min = i1),
  forall (j: Z),
  forall (Post7: j = (i1 + 1)),
  forall (j1: Z),
  forall (min1: Z),
  forall (Post3: (((i1 + 1) <= j1 /\ j1 <= (array_length t0)) /\ (i1 <=
                 min1 /\ min1 < (array_length t0)) /\
                 (forall (k:Z),
                  (i1 <= k /\ k < j1 -> (access t0 min1) <= (access t0 k)))) /\
                 j1 >= (array_length t0)),
  0 <= min1 /\ min1 < (array_length t0).
Proof.
intuition.
Qed.

(* Why obligation from file "selection.mlw", characters 926-931 *)
Lemma selection_po_7 : 
  forall (t: (array Z)),
  forall (Pre19: (array_length t) >= 1),
  forall (i: Z),
  forall (Post11: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Pre18: Variant1 = ((array_length t0) - i1)),
  forall (Pre17: (0 <= i1 /\ i1 <= ((array_length t0) - 1)) /\
                 (sorted_array t0 0 (i1 - 1)) /\ (permut t0 t) /\
                 (forall (k:Z),
                  (0 <= k /\ k < i1 ->
                   (forall (l:Z),
                    (i1 <= l /\ l < (array_length t0) -> (access t0 k) <=
                     (access t0 l)))))),
  forall (Test6: i1 < ((array_length t0) - 1)),
  forall (min: Z),
  forall (Post8: min = i1),
  forall (j: Z),
  forall (Post7: j = (i1 + 1)),
  forall (j1: Z),
  forall (min1: Z),
  forall (Post3: (((i1 + 1) <= j1 /\ j1 <= (array_length t0)) /\ (i1 <=
                 min1 /\ min1 < (array_length t0)) /\
                 (forall (k:Z),
                  (i1 <= k /\ k < j1 -> (access t0 min1) <= (access t0 k)))) /\
                 j1 >= (array_length t0)),
  forall (Pre16: 0 <= min1 /\ min1 < (array_length t0)),
  forall (w: Z),
  forall (Post6: w = (access t0 min1)),
  forall (Pre14: 0 <= min1 /\ min1 < (array_length t0)),
  0 <= i1 /\ i1 < (array_length t0).
Proof.
intuition.
Qed.

(* Why obligation from file "selection.mlw", characters 933-943 *)
Lemma selection_po_8 : 
  forall (t: (array Z)),
  forall (Pre19: (array_length t) >= 1),
  forall (i: Z),
  forall (Post11: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Pre18: Variant1 = ((array_length t0) - i1)),
  forall (Pre17: (0 <= i1 /\ i1 <= ((array_length t0) - 1)) /\
                 (sorted_array t0 0 (i1 - 1)) /\ (permut t0 t) /\
                 (forall (k:Z),
                  (0 <= k /\ k < i1 ->
                   (forall (l:Z),
                    (i1 <= l /\ l < (array_length t0) -> (access t0 k) <=
                     (access t0 l)))))),
  forall (Test6: i1 < ((array_length t0) - 1)),
  forall (min: Z),
  forall (Post8: min = i1),
  forall (j: Z),
  forall (Post7: j = (i1 + 1)),
  forall (j1: Z),
  forall (min1: Z),
  forall (Post3: (((i1 + 1) <= j1 /\ j1 <= (array_length t0)) /\ (i1 <=
                 min1 /\ min1 < (array_length t0)) /\
                 (forall (k:Z),
                  (i1 <= k /\ k < j1 -> (access t0 min1) <= (access t0 k)))) /\
                 j1 >= (array_length t0)),
  forall (Pre16: 0 <= min1 /\ min1 < (array_length t0)),
  forall (w: Z),
  forall (Post6: w = (access t0 min1)),
  forall (Pre14: 0 <= min1 /\ min1 < (array_length t0)),
  forall (Pre15: 0 <= i1 /\ i1 < (array_length t0)),
  forall (t1: (array Z)),
  forall (Post4: t1 = (store t0 min1 (access t0 i1))),
  0 <= i1 /\ i1 < (array_length t1).
Proof.
intuition.
ArraySubst t1.
Qed.

(* Why obligation from file "selection.mlw", characters 909-947 *)
Lemma selection_po_9 : 
  forall (t: (array Z)),
  forall (Pre19: (array_length t) >= 1),
  forall (i: Z),
  forall (Post11: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Pre18: Variant1 = ((array_length t0) - i1)),
  forall (Pre17: (0 <= i1 /\ i1 <= ((array_length t0) - 1)) /\
                 (sorted_array t0 0 (i1 - 1)) /\ (permut t0 t) /\
                 (forall (k:Z),
                  (0 <= k /\ k < i1 ->
                   (forall (l:Z),
                    (i1 <= l /\ l < (array_length t0) -> (access t0 k) <=
                     (access t0 l)))))),
  forall (Test6: i1 < ((array_length t0) - 1)),
  forall (min: Z),
  forall (Post8: min = i1),
  forall (j: Z),
  forall (Post7: j = (i1 + 1)),
  forall (j1: Z),
  forall (min1: Z),
  forall (Post3: (((i1 + 1) <= j1 /\ j1 <= (array_length t0)) /\ (i1 <=
                 min1 /\ min1 < (array_length t0)) /\
                 (forall (k:Z),
                  (i1 <= k /\ k < j1 -> (access t0 min1) <= (access t0 k)))) /\
                 j1 >= (array_length t0)),
  forall (Pre16: 0 <= min1 /\ min1 < (array_length t0)),
  forall (w: Z),
  forall (Post6: w = (access t0 min1)),
  forall (Pre14: 0 <= min1 /\ min1 < (array_length t0)),
  forall (Pre15: 0 <= i1 /\ i1 < (array_length t0)),
  forall (t1: (array Z)),
  forall (Post4: t1 = (store t0 min1 (access t0 i1))),
  forall (Pre13: 0 <= i1 /\ i1 < (array_length t1)),
  forall (t2: (array Z)),
  forall (Post5: t2 = (store t1 i1 w)),
  (forall (i:Z),
   (i = (i1 + 1) -> ((0 <= i /\ i <= ((array_length t2) - 1)) /\
    (sorted_array t2 0 (i - 1)) /\ (permut t2 t) /\
    (forall (k:Z),
     (0 <= k /\ k < i ->
      (forall (l:Z),
       (i <= l /\ l < (array_length t2) -> (access t2 k) <= (access t2 l)))))) /\
    (Zwf 0 ((array_length t2) - i) ((array_length t0) - i1)))).
Proof.
intuition.
ArraySubst t2.
ArraySubst t1.
assert h: i1 = 0%Z \/ (0 < i1)%Z.
 omega.
 intuition.
replace (i0 - 1)%Z with 0%Z.
unfold sorted_array; intros; omega.
omega.
replace (i0 - 1)%Z with (i1 - 1 + 1)%Z.
apply right_extension.
omega.
ArraySubst t2.
ArraySubst t1.
apply sorted_array_id with t0.
assumption.
unfold array_id; intros.
subst t2; do 2 AccessOther.
replace (i1 - 1 + 1)%Z with i1.
subst t2 t1; do 2 AccessOther.
subst w.
apply H4; omega.
omega.
omega.
apply permut_trans with t0.
subst t2; subst t1; subst w.
apply exchange_is_permut with min1 i1; auto with *.
assumption.
assert h: k = i1 \/ (k < i1)%Z.
 omega.
 intuition.
subst k.
subst t2; simpl in H23.
AccessSame.
AccessOther.
subst t1; simpl in H23.
assert h: l = min1 \/ min1 <> l.
 omega.
 intuition.
subst l; AccessSame.
subst w; apply H11; omega.
AccessOther.
subst w; apply H11; try omega.
subst t2; simpl in H23.
 AccessOther.
AccessOther.
subst t1; simpl in H23.
assert h: l = min1 \/ min1 <> l.
 omega.
 intuition.
subst l; AccessSame.
AccessOther.
apply H4; omega.
AccessOther.
AccessOther.
apply H4; omega.
subst t2 t1; simpl; unfold Zwf; omega.
Qed.

(* Why obligation from file "selection.mlw", characters 232-424 *)
Lemma selection_po_10 : 
  forall (t: (array Z)),
  forall (Pre19: (array_length t) >= 1),
  forall (i: Z),
  forall (Post11: i = 0),
  (0 <= i /\ i <= ((array_length t) - 1)) /\ (sorted_array t 0 (i - 1)) /\
  (permut t t) /\
  (forall (k:Z),
   (0 <= k /\ k < i ->
    (forall (l:Z),
     (i <= l /\ l < (array_length t) -> (access t k) <= (access t l))))).
Proof.
intuition.
unfold sorted_array; intros; omega.
Qed.

(* Why obligation from file "selection.mlw", characters 120-985 *)
Lemma selection_po_11 : 
  forall (t: (array Z)),
  forall (Pre19: (array_length t) >= 1),
  forall (i: Z),
  forall (Post11: i = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post10: ((0 <= i1 /\ i1 <= ((array_length t0) - 1)) /\
                  (sorted_array t0 0 (i1 - 1)) /\ (permut t0 t) /\
                  (forall (k:Z),
                   (0 <= k /\ k < i1 ->
                    (forall (l:Z),
                     (i1 <= l /\ l < (array_length t0) -> (access t0 k) <=
                      (access t0 l)))))) /\
                  i1 >= ((array_length t0) - 1)),
  (sorted_array t0 0 ((array_length t0) - 1)) /\ (permut t0 t).
Proof.
intuition.
assert h: i1 = 0%Z \/ (0 < i1)%Z.
 omega.
 intuition.
unfold sorted_array; intros; omega.
replace (array_length t0 - 1)%Z with (i1 - 1 + 1)%Z.
apply right_extension; try omega.
 assumption.
apply H5; omega.
omega.
Qed.


