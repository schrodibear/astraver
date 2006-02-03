(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma swap_po_1 : 
  forall (i: Z),
  forall (j: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= i /\ i < (array_length t)) /\ 0 <= j /\ j <
                (array_length t)),
  forall (HW_2: 0 <= i /\ i < (array_length t)),
  forall (result: Z),
  forall (HW_3: result = (access t i)),
  forall (HW_4: 0 <= j /\ j < (array_length t)),
  forall (result0: Z),
  forall (HW_5: result0 = (access t j)),
  forall (HW_6: 0 <= i /\ i < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_7: t0 = (update t i result0)),
  0 <= j /\ j < (array_length t0).
Proof.
tauto.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma swap_po_2 : 
  forall (i: Z),
  forall (j: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= i /\ i < (array_length t)) /\ 0 <= j /\ j <
                (array_length t)),
  forall (HW_2: 0 <= i /\ i < (array_length t)),
  forall (result: Z),
  forall (HW_3: result = (access t i)),
  forall (HW_4: 0 <= j /\ j < (array_length t)),
  forall (result0: Z),
  forall (HW_5: result0 = (access t j)),
  forall (HW_6: 0 <= i /\ i < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_7: t0 = (update t i result0)),
  forall (HW_8: 0 <= j /\ j < (array_length t0)),
  forall (t1: (array Z)),
  forall (HW_9: t1 = (update t0 j result)),
  (exchange t1 t i j).
Proof.
intros; ArraySubst t0.
Qed.


Proof.
intros; subst t1; subst t0; subst v.
auto with datatypes.
Qed.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_1 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_2: l < r),
  0 <= l /\ l < (array_length t).
Proof.
auto with *.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_2 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_2: l < r),
  forall (HW_3: 0 <= l /\ l < (array_length t)),
  forall (result: Z),
  forall (HW_4: result = (access t l)),
  (forall (j:Z), (l < j /\ j <= l -> (access t j) < result)) /\
  (forall (j:Z), (l < j /\ j < (l + 1) -> (access t j) >= result)) /\
  (sub_permut l r t t) /\ (access t l) = result /\ (l <= l /\ l < (l + 1)) /\
  (l + 1) <= (r + 1).
Proof.
intuition.
ArrayLength.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_3 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_2: l < r),
  forall (HW_3: 0 <= l /\ l < (array_length t)),
  forall (result: Z),
  forall (HW_4: result = (access t l)),
  forall (HW_5: (forall (j:Z), (l < j /\ j <= l -> (access t j) < result)) /\
                (forall (j:Z),
                 (l < j /\ j < (l + 1) -> (access t j) >= result)) /\
                (sub_permut l r t t) /\ (access t l) = result /\ (l <= l /\
                l < (l + 1)) /\ (l + 1) <= (r + 1)),
  forall (i: Z),
  forall (m: Z),
  forall (t0: (array Z)),
  forall (HW_6: (forall (j:Z), (l < j /\ j <= m -> (access t0 j) < result)) /\
                (forall (j:Z), (m < j /\ j < i -> (access t0 j) >= result)) /\
                (sub_permut l r t0 t) /\ (access t0 l) = result /\ (l <= m /\
                m < i) /\ i <= (r + 1)),
  forall (HW_7: i <= r),
  0 <= i /\ i < (array_length t0).
Proof.
intuition ArrayLength; omega.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_4 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_2: l < r),
  forall (HW_3: 0 <= l /\ l < (array_length t)),
  forall (result: Z),
  forall (HW_4: result = (access t l)),
  forall (HW_5: (forall (j:Z), (l < j /\ j <= l -> (access t j) < result)) /\
                (forall (j:Z),
                 (l < j /\ j < (l + 1) -> (access t j) >= result)) /\
                (sub_permut l r t t) /\ (access t l) = result /\ (l <= l /\
                l < (l + 1)) /\ (l + 1) <= (r + 1)),
  forall (i: Z),
  forall (m: Z),
  forall (t0: (array Z)),
  forall (HW_6: (forall (j:Z), (l < j /\ j <= m -> (access t0 j) < result)) /\
                (forall (j:Z), (m < j /\ j < i -> (access t0 j) >= result)) /\
                (sub_permut l r t0 t) /\ (access t0 l) = result /\ (l <= m /\
                m < i) /\ i <= (r + 1)),
  forall (HW_7: i <= r),
  forall (HW_8: 0 <= i /\ i < (array_length t0)),
  forall (result0: Z),
  forall (HW_9: result0 = (access t0 i)),
  forall (HW_10: result0 < result),
  forall (m0: Z),
  forall (HW_11: m0 = (m + 1)),
  (0 <= i /\ i < (array_length t0)) /\ 0 <= m0 /\ m0 < (array_length t0).
Proof.
intuition.
assert (hj: (j < m2)%Z \/ j = m2).
 omega.
 decompose [exchange] Post30.
 intuition.
rewrite H26; try omega.
apply H5; omega.
subst j; rewrite H25; assumption.
assert (hj: (j < i1)%Z \/ j = i1).
 omega.
 decompose [exchange] Post30.
 intuition.
rewrite H26; try omega.
apply H9; omega.
subst j; rewrite H24.
 apply H9; omega.
apply sub_permut_trans with t1.
apply exchange_is_sub_permut with i1 m2; assumption || omega.
assumption.
decompose [exchange] Post30.
 intuition.
rewrite H24; omega.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_5 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_2: l < r),
  forall (HW_3: 0 <= l /\ l < (array_length t)),
  forall (result: Z),
  forall (HW_4: result = (access t l)),
  forall (HW_5: (forall (j:Z), (l < j /\ j <= l -> (access t j) < result)) /\
                (forall (j:Z),
                 (l < j /\ j < (l + 1) -> (access t j) >= result)) /\
                (sub_permut l r t t) /\ (access t l) = result /\ (l <= l /\
                l < (l + 1)) /\ (l + 1) <= (r + 1)),
  forall (i: Z),
  forall (m: Z),
  forall (t0: (array Z)),
  forall (HW_6: (forall (j:Z), (l < j /\ j <= m -> (access t0 j) < result)) /\
                (forall (j:Z), (m < j /\ j < i -> (access t0 j) >= result)) /\
                (sub_permut l r t0 t) /\ (access t0 l) = result /\ (l <= m /\
                m < i) /\ i <= (r + 1)),
  forall (HW_7: i <= r),
  forall (HW_8: 0 <= i /\ i < (array_length t0)),
  forall (result0: Z),
  forall (HW_9: result0 = (access t0 i)),
  forall (HW_10: result0 < result),
  forall (m0: Z),
  forall (HW_11: m0 = (m + 1)),
  forall (HW_12: (0 <= i /\ i < (array_length t0)) /\ 0 <= m0 /\ m0 <
                 (array_length t0)),
  forall (t1: (array Z)),
  forall (HW_13: (exchange t1 t0 i m0)),
  forall (i0: Z),
  forall (HW_14: i0 = (i + 1)),
  ((forall (j:Z), (l < j /\ j <= m0 -> (access t1 j) < result)) /\
  (forall (j:Z), (m0 < j /\ j < i0 -> (access t1 j) >= result)) /\
  (sub_permut l r t1 t) /\ (access t1 l) = result /\ (l <= m0 /\ m0 < i0) /\
  i0 <= (r + 1)) /\ (Zwf 0 (1 + r - i0) (1 + r - i)).
Proof.
intuition.
assert (hj: (j < i1)%Z \/ j = i1).
 omega.
 intuition.
rewrite H15; assumption.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_6 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_2: l < r),
  forall (HW_3: 0 <= l /\ l < (array_length t)),
  forall (result: Z),
  forall (HW_4: result = (access t l)),
  forall (HW_5: (forall (j:Z), (l < j /\ j <= l -> (access t j) < result)) /\
                (forall (j:Z),
                 (l < j /\ j < (l + 1) -> (access t j) >= result)) /\
                (sub_permut l r t t) /\ (access t l) = result /\ (l <= l /\
                l < (l + 1)) /\ (l + 1) <= (r + 1)),
  forall (i: Z),
  forall (m: Z),
  forall (t0: (array Z)),
  forall (HW_6: (forall (j:Z), (l < j /\ j <= m -> (access t0 j) < result)) /\
                (forall (j:Z), (m < j /\ j < i -> (access t0 j) >= result)) /\
                (sub_permut l r t0 t) /\ (access t0 l) = result /\ (l <= m /\
                m < i) /\ i <= (r + 1)),
  forall (HW_7: i <= r),
  forall (HW_8: 0 <= i /\ i < (array_length t0)),
  forall (result0: Z),
  forall (HW_9: result0 = (access t0 i)),
  forall (HW_15: result0 >= result),
  forall (i0: Z),
  forall (HW_16: i0 = (i + 1)),
  ((forall (j:Z), (l < j /\ j <= m -> (access t0 j) < result)) /\
  (forall (j:Z), (m < j /\ j < i0 -> (access t0 j) >= result)) /\
  (sub_permut l r t0 t) /\ (access t0 l) = result /\ (l <= m /\ m < i0) /\
  i0 <= (r + 1)) /\ (Zwf 0 (1 + r - i0) (1 + r - i)).
Proof.
intuition.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_7 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_2: l < r),
  forall (HW_3: 0 <= l /\ l < (array_length t)),
  forall (result: Z),
  forall (HW_4: result = (access t l)),
  forall (HW_5: (forall (j:Z), (l < j /\ j <= l -> (access t j) < result)) /\
                (forall (j:Z),
                 (l < j /\ j < (l + 1) -> (access t j) >= result)) /\
                (sub_permut l r t t) /\ (access t l) = result /\ (l <= l /\
                l < (l + 1)) /\ (l + 1) <= (r + 1)),
  forall (i: Z),
  forall (m: Z),
  forall (t0: (array Z)),
  forall (HW_6: (forall (j:Z), (l < j /\ j <= m -> (access t0 j) < result)) /\
                (forall (j:Z), (m < j /\ j < i -> (access t0 j) >= result)) /\
                (sub_permut l r t0 t) /\ (access t0 l) = result /\ (l <= m /\
                m < i) /\ i <= (r + 1)),
  forall (HW_17: i > r),
  (0 <= l /\ l < (array_length t0)) /\ 0 <= m /\ m < (array_length t0).
Proof.
intuition ArrayLength; omega.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_8 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_2: l < r),
  forall (HW_3: 0 <= l /\ l < (array_length t)),
  forall (result: Z),
  forall (HW_4: result = (access t l)),
  forall (HW_5: (forall (j:Z), (l < j /\ j <= l -> (access t j) < result)) /\
                (forall (j:Z),
                 (l < j /\ j < (l + 1) -> (access t j) >= result)) /\
                (sub_permut l r t t) /\ (access t l) = result /\ (l <= l /\
                l < (l + 1)) /\ (l + 1) <= (r + 1)),
  forall (i: Z),
  forall (m: Z),
  forall (t0: (array Z)),
  forall (HW_6: (forall (j:Z), (l < j /\ j <= m -> (access t0 j) < result)) /\
                (forall (j:Z), (m < j /\ j < i -> (access t0 j) >= result)) /\
                (sub_permut l r t0 t) /\ (access t0 l) = result /\ (l <= m /\
                m < i) /\ i <= (r + 1)),
  forall (HW_17: i > r),
  forall (HW_18: (0 <= l /\ l < (array_length t0)) /\ 0 <= m /\ m <
                 (array_length t0)),
  forall (t1: (array Z)),
  forall (HW_19: (exchange t1 t0 l m)),
  (Zwf 0 (1 + (m - 1) - l) (1 + r - l)).
Proof.
intuition ArrayLength.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_9 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_2: l < r),
  forall (HW_3: 0 <= l /\ l < (array_length t)),
  forall (result: Z),
  forall (HW_4: result = (access t l)),
  forall (HW_5: (forall (j:Z), (l < j /\ j <= l -> (access t j) < result)) /\
                (forall (j:Z),
                 (l < j /\ j < (l + 1) -> (access t j) >= result)) /\
                (sub_permut l r t t) /\ (access t l) = result /\ (l <= l /\
                l < (l + 1)) /\ (l + 1) <= (r + 1)),
  forall (i: Z),
  forall (m: Z),
  forall (t0: (array Z)),
  forall (HW_6: (forall (j:Z), (l < j /\ j <= m -> (access t0 j) < result)) /\
                (forall (j:Z), (m < j /\ j < i -> (access t0 j) >= result)) /\
                (sub_permut l r t0 t) /\ (access t0 l) = result /\ (l <= m /\
                m < i) /\ i <= (r + 1)),
  forall (HW_17: i > r),
  forall (HW_18: (0 <= l /\ l < (array_length t0)) /\ 0 <= m /\ m <
                 (array_length t0)),
  forall (t1: (array Z)),
  forall (HW_19: (exchange t1 t0 l m)),
  forall (HW_20: (Zwf 0 (1 + (m - 1) - l) (1 + r - l))),
  0 <= l /\ (m - 1) < (array_length t1).
Proof.
intuition.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_10 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_2: l < r),
  forall (HW_3: 0 <= l /\ l < (array_length t)),
  forall (result: Z),
  forall (HW_4: result = (access t l)),
  forall (HW_5: (forall (j:Z), (l < j /\ j <= l -> (access t j) < result)) /\
                (forall (j:Z),
                 (l < j /\ j < (l + 1) -> (access t j) >= result)) /\
                (sub_permut l r t t) /\ (access t l) = result /\ (l <= l /\
                l < (l + 1)) /\ (l + 1) <= (r + 1)),
  forall (i: Z),
  forall (m: Z),
  forall (t0: (array Z)),
  forall (HW_6: (forall (j:Z), (l < j /\ j <= m -> (access t0 j) < result)) /\
                (forall (j:Z), (m < j /\ j < i -> (access t0 j) >= result)) /\
                (sub_permut l r t0 t) /\ (access t0 l) = result /\ (l <= m /\
                m < i) /\ i <= (r + 1)),
  forall (HW_17: i > r),
  forall (HW_18: (0 <= l /\ l < (array_length t0)) /\ 0 <= m /\ m <
                 (array_length t0)),
  forall (t1: (array Z)),
  forall (HW_19: (exchange t1 t0 l m)),
  forall (HW_20: (Zwf 0 (1 + (m - 1) - l) (1 + r - l))),
  forall (HW_21: 0 <= l /\ (m - 1) < (array_length t1)),
  forall (t2: (array Z)),
  forall (HW_22: (sorted_array t2 l (m - 1)) /\ (sub_permut l (m - 1) t2 t1)),
  (Zwf 0 (1 + r - (m + 1)) (1 + r - l)).
Proof.
intuition.
generalize (sub_permut_length H20); generalize (exchange_length Post32);
 generalize (sub_permut_length H10); intros; omega.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_11 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_2: l < r),
  forall (HW_3: 0 <= l /\ l < (array_length t)),
  forall (result: Z),
  forall (HW_4: result = (access t l)),
  forall (HW_5: (forall (j:Z), (l < j /\ j <= l -> (access t j) < result)) /\
                (forall (j:Z),
                 (l < j /\ j < (l + 1) -> (access t j) >= result)) /\
                (sub_permut l r t t) /\ (access t l) = result /\ (l <= l /\
                l < (l + 1)) /\ (l + 1) <= (r + 1)),
  forall (i: Z),
  forall (m: Z),
  forall (t0: (array Z)),
  forall (HW_6: (forall (j:Z), (l < j /\ j <= m -> (access t0 j) < result)) /\
                (forall (j:Z), (m < j /\ j < i -> (access t0 j) >= result)) /\
                (sub_permut l r t0 t) /\ (access t0 l) = result /\ (l <= m /\
                m < i) /\ i <= (r + 1)),
  forall (HW_17: i > r),
  forall (HW_18: (0 <= l /\ l < (array_length t0)) /\ 0 <= m /\ m <
                 (array_length t0)),
  forall (t1: (array Z)),
  forall (HW_19: (exchange t1 t0 l m)),
  forall (HW_20: (Zwf 0 (1 + (m - 1) - l) (1 + r - l))),
  forall (HW_21: 0 <= l /\ (m - 1) < (array_length t1)),
  forall (t2: (array Z)),
  forall (HW_22: (sorted_array t2 l (m - 1)) /\ (sub_permut l (m - 1) t2 t1)),
  forall (HW_23: (Zwf 0 (1 + r - (m + 1)) (1 + r - l))),
  0 <= (m + 1) /\ r < (array_length t2).
Proof.
intuition.
Qed.

Proof.
intuition.
unfold sorted_array; intros.
assert (hx: (x < m1 - 1)%Z \/ x = (m1 - 1)%Z \/ x = m1 \/ (m1 < x)).
 omega.
 intuition.
(* x < m0-1 *)
elim (sub_permut_id H24); intros.
unfold array_id in H29.
rewrite (H29 x).
 rewrite (H29 (x + 1)%Z).
 apply H19; omega.
 omega.
 omega.
(* x = m0-1 *)
elim (sub_permut_id H24); intros.
unfold array_id in H28.
rewrite (H28 x).
 rewrite (H28 (x + 1)%Z).
 clear H28 H30.
 elim (sub_permut_id H20); intros.
unfold array_id in H30.
 replace (x + 1)%Z with m1.
rewrite (H30 m1).
 elim Post32; intros.
rewrite H35.
 rewrite H13.
 clear H34 H35 H36.
assert (hm0: (m1 - 1 < array_length t2)).
 omega.
rewrite <- (sub_permut_length H20) in hm0.
generalize (sub_permut_function H20 H1 hm0); intros.
elim (H34 x).
 clear H34.
 intuition.
elim H34; intros j [H1j H2j].
rewrite H2j.
assert (j = l0 \/ (l0 < j)%Z).
 omega.
 intuition.
elim Post32; intros.
subst j.
 rewrite H44.
assert (access t1 m1 < v)%Z.
apply H9; omega.
 omega.
elim Post32; intros.
rewrite H46; try omega.
assert (access t1 j < v)%Z.
apply H9; omega.
 omega.
omega.
 omega.
 omega.
 omega.
 omega.
(* x = m0 *)
subst x.
elim (sub_permut_id H24); intros.
unfold array_id in H28.
rewrite (H28 m1).
 clear H28 H29.
assert (hm0: (0 <= m1 + 1)).
 omega.
assert (hl: array_length t4 = array_length t0).
  ArrayLength; clear H24.
  ArrayLength; clear H20.
  ArrayLength; clear Post32.
  ArrayLength.
rewrite <- hl in H2.
generalize (sub_permut_function H24 hm0 H2); intros.
elim (H28 (m1 + 1)%Z).
 clear H28.
 intuition.
elim H28; intros j [H1j H2j].
 rewrite H2j.
clear H28 H29 H2j.
elim (sub_permut_id H20); intros.
unfold array_id in H29.
rewrite (H29 m1); try omega.
 rewrite (H29 j); try omega.
elim Post32; intros.
rewrite H34.
rewrite (H35 j); try omega.
rewrite H13.
apply Zge_le.
apply H8; omega.
 ArrayLength; clear Post32; ArrayLength.
 omega.
 omega.
(* sub_permut *)
apply sub_permut_trans with t3.
apply sub_permut_extension with (m1 + 1)%Z r0.
omega.
 omega.
 assumption.
apply sub_permut_trans with t2.
apply sub_permut_extension with l0 (m1 - 1)%Z.
omega.
 omega.
 assumption.
apply sub_permut_trans with t1.
apply exchange_is_sub_permut with l0 m1.
omega.
 omega.
 assumption.
assumption.
Qed.

Proof.
intuition.
unfold sorted_array; intros; omega.
Qed.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_12 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_2: l < r),
  forall (HW_3: 0 <= l /\ l < (array_length t)),
  forall (result: Z),
  forall (HW_4: result = (access t l)),
  forall (HW_5: (forall (j:Z), (l < j /\ j <= l -> (access t j) < result)) /\
                (forall (j:Z),
                 (l < j /\ j < (l + 1) -> (access t j) >= result)) /\
                (sub_permut l r t t) /\ (access t l) = result /\ (l <= l /\
                l < (l + 1)) /\ (l + 1) <= (r + 1)),
  forall (i: Z),
  forall (m: Z),
  forall (t0: (array Z)),
  forall (HW_6: (forall (j:Z), (l < j /\ j <= m -> (access t0 j) < result)) /\
                (forall (j:Z), (m < j /\ j < i -> (access t0 j) >= result)) /\
                (sub_permut l r t0 t) /\ (access t0 l) = result /\ (l <= m /\
                m < i) /\ i <= (r + 1)),
  forall (HW_17: i > r),
  forall (HW_18: (0 <= l /\ l < (array_length t0)) /\ 0 <= m /\ m <
                 (array_length t0)),
  forall (t1: (array Z)),
  forall (HW_19: (exchange t1 t0 l m)),
  forall (HW_20: (Zwf 0 (1 + (m - 1) - l) (1 + r - l))),
  forall (HW_21: 0 <= l /\ (m - 1) < (array_length t1)),
  forall (t2: (array Z)),
  forall (HW_22: (sorted_array t2 l (m - 1)) /\ (sub_permut l (m - 1) t2 t1)),
  forall (HW_23: (Zwf 0 (1 + r - (m + 1)) (1 + r - l))),
  forall (HW_24: 0 <= (m + 1) /\ r < (array_length t2)),
  forall (t3: (array Z)),
  forall (HW_25: (sorted_array t3 (m + 1) r) /\ (sub_permut (m + 1) r t3 t2)),
  (sorted_array t3 l r) /\ (sub_permut l r t3 t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quick_rec_po_13 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (HW_1: 0 <= l /\ r < (array_length t)),
  forall (HW_26: l >= r),
  (sorted_array t l r) /\ (sub_permut l r t t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quicksort_po_1 : 
  forall (t: (array Z)),
  forall (result: Z),
  forall (HW_1: result = (array_length t)),
  0 <= 0 /\ (result - 1) < (array_length t).
Proof.
intuition omega.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma quicksort_po_2 : 
  forall (t: (array Z)),
  forall (result: Z),
  forall (HW_1: result = (array_length t)),
  forall (HW_2: 0 <= 0 /\ (result - 1) < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_3: (sorted_array t0 0 (result - 1)) /\
                (sub_permut 0 (result - 1) t0 t)),
  (sorted_array t0 0 ((array_length t0) - 1)) /\ (permut t0 t).
Proof.
intuition.
ArrayLength; assumption.
eauto.
Qed.


