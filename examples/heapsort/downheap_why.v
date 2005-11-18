(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Import Omega.
Require Export heap.
Require Export Inftree.

Lemma R11 : forall k:Z, (2 * k + 1 + 1)%Z = (2 * k + 2)%Z.
Proof.
intro; omega.
Qed.

(* To annotate the recursive function downheap, it is convenient to
 * introduce the following predicate, which expresses that j is the
 * greatest son of k. *)

Set Implicit Arguments.
Unset Strict Implicit.

Inductive select_son (t:array Z) (k n j:Z) : Prop :=
  | select_left_son :
      j = (2 * k + 1)%Z ->
      ((2 * k + 2 <= n)%Z -> (access t j >= access t (2 * k + 2))%Z) ->
      select_son t k n j
  | select_right_son :
      j = (2 * k + 2)%Z ->
      (j <= n)%Z ->
      (access t j >= access t (2 * k + 1))%Z -> select_son t k n j.

Set Strict Implicit.
Unset Implicit Arguments.

(* The correctness of downheap requires the two following lemmas *)

Lemma Lemma_1 :
 forall (t0 t1 t2:array Z) (n0 k0 j':Z),
   (2 * k0 + 1 <= n0)%Z ->
   select_son t0 k0 n0 j' ->
   (access t0 k0 < access t0 j')%Z ->
   exchange t1 t0 k0 j' ->
   (0 <= k0 <= n0)%Z ->
   (n0 < array_length t0)%Z ->
   (forall i:Z, (k0 + 1 <= i <= n0)%Z -> heap t0 n0 i) ->
   (forall i:Z, (j' <= i <= n0)%Z -> heap t2 n0 i) ->
   (forall i:Z,
      (0 <= i < j')%Z \/
      (j' < i < 2 * j' + 1)%Z \/ (n0 < i < array_length t0)%Z ->
      access t2 i = access t1 i) ->
   (forall v:Z, inftree t1 n0 v j' -> inftree t2 n0 v j') ->
   forall i:Z, (k0 < i < j')%Z -> heap t2 n0 i.
Proof.
intros.
 apply heap_cons.
elim H0; Omega'.
(* branch 2i+1 *)
intro.
 rewrite (H7 i).
 rewrite (H7 (2 * i + 1)%Z).
decompose [exchange] H2.
 rewrite (H16 i).
 rewrite (H16 (2 * i + 1)%Z).
generalize H10.
 elim (H5 i); intros.
 exact (H18 H24).
Omega'.
 Omega'.
 Omega'.
elim H0; Omega'.
 Omega'.
 Omega'.
 Omega'.
elim H0; Omega'.
 elim H0; Omega'.
 intro.
 apply H6; elim H0; Omega'.
(* branch 2i+2 *)
intro.
 rewrite (H7 i).
 rewrite (H7 (2 * i + 2)%Z).
decompose [exchange] H2.
 rewrite (H16 i).
 rewrite (H16 (2 * i + 2)%Z).
generalize H10.
 elim (H5 i); intros.
 exact (H21 H24).
Omega'.
 Omega'.
 Omega'.
 elim H0; Omega'.
 Omega'.
 Omega'.
 Omega'.
elim H0; Omega'.
 elim H0; Omega'.
 intro.
 apply H6; elim H0; Omega'.
Qed.

Lemma Lemma_2 :
 forall (t0 t1 t2:array Z) (n0 k0 j':Z),
   (2 * k0 + 1 <= n0)%Z ->
   select_son t0 k0 n0 j' ->
   (access t0 k0 < access t0 j')%Z ->
   exchange t1 t0 k0 j' ->
   (0 <= k0 <= n0)%Z ->
   (n0 < array_length t0)%Z ->
   (forall i:Z, (k0 + 1 <= i <= n0)%Z -> heap t0 n0 i) ->
   (forall i:Z, (j' <= i <= n0)%Z -> heap t2 n0 i) ->
   (forall i:Z,
      (0 <= i < j')%Z \/
      (j' < i < 2 * j' + 1)%Z \/ (n0 < i < array_length t0)%Z ->
      access t2 i = access t1 i) ->
   (forall v:Z, inftree t1 n0 v j' -> inftree t2 n0 v j') ->
   forall i:Z, (k0 <= i <= n0)%Z -> heap t2 n0 i.
Proof.
intros.
elim (Z_lt_ge_dec i j'); intro HHi.
elim (Z_le_lt_eq_dec k0 i); [ intro HHHi | intro HHHi | intuition ].

(* 1. k0 < i < j' *)
apply (Lemma_1 t0 t1 t2 n0 k0 j'); assumption || Omega'.

(* 2. k0 = i *)
apply heap_cons.
Omega'.
(* branch 2i+1 *)
(* t[k] >= t[2k+1] *)
intro.
 elim H0; intros.
  (* j' = 2k+1 *)
  rewrite <- HHHi.
 rewrite <- H11.
  rewrite (H7 k0).
 decompose [exchange] H2.
 rewrite H16.
  apply Zle_ge.
 apply inftree_1 with (n := n0).
  apply H8.
  apply inftree_2 with (t1 := t0) (k := k0).
 Omega'.
   apply inftree_3.
  apply H5; Omega'.
 assumption.
 Omega'.
 Omega'.
 Omega'.
  (* j' = 2k+2 *)
  rewrite <- HHHi.
  rewrite (H7 k0).
 decompose [exchange] H2.
 rewrite H17.
  rewrite (H7 (2 * k0 + 1)%Z).
 rewrite (H19 (2 * k0 + 1)%Z).
  Omega'.
 Omega'.
 Omega'.
 Omega'.
 Omega'.
 Omega'.
 (* (heap t2 n (2k+1)) *)
intro.
 elim H0; intros.
  (* j' = 2k+1 *)
  apply H6; Omega'.
  (* j' = 2k+2 *)
  apply (Lemma_1 t0 t1 t2 n0 k0 j'); assumption || Omega'.
(* branch 2i+2 *)
(* t[k] >= t[2k+2] *)
intro.
 elim H0; intros.
  (* j' = 2k+1 *)
  rewrite <- HHHi.
  rewrite (H7 k0).
 decompose [exchange] H2.
 rewrite H16.
  rewrite (H7 (2 * k0 + 2)%Z).
 rewrite (H18 (2 * k0 + 2)%Z).
  Omega'.
 Omega'.
 Omega'.
 Omega'.
 Omega'.
 Omega'.
   (* j' = 2k+2 *)
  rewrite <- HHHi.
 rewrite <- H11.
  rewrite (H7 k0).
 decompose [exchange] H2.
 rewrite H17.
  apply Zle_ge.
 apply inftree_1 with (n := n0).
  apply H8.
  apply inftree_2 with (t1 := t0) (k := k0).
 Omega'.
   apply inftree_3.
  apply H5; Omega'.
 assumption.
 Omega'.
 Omega'.
 Omega'.
(* (heap t2 n (2k+2)) *)
intro.
 elim H0; intros.
  (* j' = 2k+1 *)
  apply H6; Omega'.
  (* j' = 2k+2 *)
  apply H6; Omega'.

(* 3. i >= j' *)
apply H6; Omega'.
Qed.


(* Obligations *)

Proof.
intros; Omega'.
Qed.

Proof.
intros; Omega'.
Qed.

Proof.
intros.
subst j; rewrite (R11 k0).
apply select_right_son;
 [ reflexivity | Omega' | rewrite (R11 k0) in Test4; Omega' ].
Qed.

Proof.
intros.
subst j.
apply select_left_son;
 [ reflexivity | rewrite (R11 k0) in Test3; intro; assumption ].
Qed.

Proof.
intros.
subst j.
apply select_left_son;
 [ reflexivity | intro; absurd (2 * k + 2 <= n)%Z; Omega' ].
Qed.

Proof.
intros; elim Post12; intros; Omega'.
Qed.

Proof.
intros; elim Post12; intros; Omega'.
Qed.

Proof.
intuition; try (elim Post12; SameLength t1 t0; Omega').
apply heap_id with (t := t0).
apply H7; elim Post12; Omega'.
unfold array_id.
 intros i' Hi'.
elim Post23; intros.
symmetry; apply (H22 i'); elim Post12; Omega'.
Qed.

Proof.
intros; unfold Zwf; decompose [select_son] Post12; Omega'.
Qed.

Proof.
trivial.
Qed.

Proof.
intuition.
(* permut *)
apply permut_trans with (t' := t1).
intuition.
 apply exchange_is_permut with (i := k0) (j := j'); assumption.
(* heap *)
apply (Lemma_2 t0 t1 t2 n0 k0 j'); assumption || (try Omega').
SameLength t2 t1.
 SameLength t1 t0.
rewrite <- H26; rewrite <- H22; assumption.
(* unchanged parts of the array *)
rewrite (H20 i); [ decompose [exchange] Post23; apply H30 | idtac ];
 decompose [select_son] Post12; Omega'.
rewrite (H20 i); [ decompose [exchange] Post23; apply H30 | idtac ];
 decompose [select_son] Post12; Omega'.
rewrite (H20 i); [ decompose [exchange] Post23; apply H30 | idtac ];
 decompose [select_son] Post12; SameLength t2 t1; Omega'.
(* inftree *)
apply inftree_cons.
split; assumption.
rewrite (H20 k0).
 decompose [exchange] Post23.
 rewrite H27.
 elim Post12; intros.
  (* j' = 2k+1 *)
  rewrite H30.
 generalize Test8; rewrite Post3.
 case H22; intros.
  apply inftree_1 with (n := n0).
 auto.
  (* j' = 2k+2 *)
  generalize H31.
 rewrite H30.
 case H22; intros.
  apply inftree_1 with (n := n0).
 auto.
elim Post12; intros; Omega'.
  (* branch 2k+1 *)
  intro.
 elim Post12; intros.
    (* j' = 2k+1 *)
    rewrite <- H25.
 apply H23.
     apply inftree_2 with (t1 := t0) (k := k0).
 Omega'.
     rewrite H25.
 generalize H24.
 case H22; auto.
    assumption.
 Omega'.
 Omega'.
    (* j' = 2k+2 *)
    apply inftree_trans with (v := access t2 (2 * k0 + 1)).
    rewrite (H20 (2 * k0 + 1)%Z).
    decompose [exchange] Post23.
 rewrite (H33 (2 * k0 + 1)%Z).
    generalize H24.
 case H22; intros.
    apply inftree_1 with (n := n0).
 auto.
    Omega'.
 Omega'.
 Omega'.
 Omega'.
    apply inftree_3.
    apply (Lemma_2 t0 t1 t2 n0 k0 j'); assumption || (try Omega').
    SameLength t2 t1.
 SameLength t1 t0.
    rewrite <- H29; rewrite <- H28; assumption.

  (* branch 2k+2 *)
  intro.
 elim Post12; intros.
    (* j' = 2k+1 *)
    apply inftree_trans with (v := access t2 (2 * k0 + 2)).
    rewrite (H20 (2 * k0 + 2)%Z).
    decompose [exchange] Post23.
 rewrite (H32 (2 * k0 + 2)%Z).
    generalize H24.
 case H22; intros.
    apply inftree_1 with (n := n0).
 auto.
    Omega'.
 Omega'.
 Omega'.
 Omega'.
    apply inftree_3.
    apply H21; Omega'.
    (* j' = 2k+2 *)
    rewrite <- H25.
 apply H23.
     apply inftree_2 with (t1 := t0) (k := k0).
 Omega'.
     rewrite H25.
 generalize H24.
 case H22; auto.
    assumption.
 Omega'.
 Omega'.
Qed.

Proof.
intuition.
elim (Z_le_lt_eq_dec k0 i); [ intro HHHi | intro HHHi | intuition ].
(* k0 < i *)
apply H7; Omega'.
(* k0 = i *)
rewrite <- HHHi.
 apply heap_cons.
Omega'.
intro.
 elim Post12; intros.
rewrite <- H14.
 assumption.
 Omega'.
intro.
 apply H7; Omega'.
intro.
 elim Post12; intros.
Omega'.
 rewrite <- H14.
 assumption.
intro.
 apply H7; Omega'.
Qed.


Proof.
intuition.
elim (Z_le_lt_eq_dec k0 i); [ intro HHHi | intro HHHi | intuition ].
apply H7; Omega'.
rewrite <- HHHi.
 apply heap_cons.
Omega'.
intro; absurd (2 * k0 + 1 > n0)%Z; Omega'.
intro; absurd (2 * k0 + 1 > n0)%Z; Omega'.
intro; absurd (2 * k0 + 2 > n0)%Z; Omega'.
intro; absurd (2 * k0 + 2 > n0)%Z; Omega'.
Qed.

Require Import swap_why.




(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_1 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_2 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_3 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_8: result < result0),
  (select_son t k n (2 * k + 1 + 1)).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_4 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_8: result < result0),
  0 <= k /\ k < (array_length t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_5 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_8: result < result0),
  forall (HW_9: 0 <= k /\ k < (array_length t)),
  forall (result1: Z),
  forall (HW_10: result1 = (access t k)),
  0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_6 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_8: result < result0),
  forall (HW_9: 0 <= k /\ k < (array_length t)),
  forall (result1: Z),
  forall (HW_10: result1 = (access t k)),
  forall (HW_11: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result2: Z),
  forall (HW_12: result2 = (access t (2 * k + 1 + 1))),
  forall (HW_13: result1 < result2),
  (0 <= k /\ k < (array_length t)) /\ 0 <= (2 * k + 1 + 1) /\
  (2 * k + 1 + 1) < (array_length t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_7 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_8: result < result0),
  forall (HW_9: 0 <= k /\ k < (array_length t)),
  forall (result1: Z),
  forall (HW_10: result1 = (access t k)),
  forall (HW_11: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result2: Z),
  forall (HW_12: result2 = (access t (2 * k + 1 + 1))),
  forall (HW_13: result1 < result2),
  forall (HW_14: (0 <= k /\ k < (array_length t)) /\ 0 <= (2 * k + 1 + 1) /\
                 (2 * k + 1 + 1) < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_15: (exchange t0 t k (2 * k + 1 + 1))),
  (Zwf 0 (n - (2 * k + 1 + 1)) (n - k)).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_8 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_8: result < result0),
  forall (HW_9: 0 <= k /\ k < (array_length t)),
  forall (result1: Z),
  forall (HW_10: result1 = (access t k)),
  forall (HW_11: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result2: Z),
  forall (HW_12: result2 = (access t (2 * k + 1 + 1))),
  forall (HW_13: result1 < result2),
  forall (HW_14: (0 <= k /\ k < (array_length t)) /\ 0 <= (2 * k + 1 + 1) /\
                 (2 * k + 1 + 1) < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_15: (exchange t0 t k (2 * k + 1 + 1))),
  forall (HW_16: (Zwf 0 (n - (2 * k + 1 + 1)) (n - k))),
  (0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) <= n) /\ n < (array_length t0) /\
  (forall (i:Z), ((2 * k + 1 + 1 + 1) <= i /\ i <= n -> (heap t0 n i))).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_9 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_8: result < result0),
  forall (HW_9: 0 <= k /\ k < (array_length t)),
  forall (result1: Z),
  forall (HW_10: result1 = (access t k)),
  forall (HW_11: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result2: Z),
  forall (HW_12: result2 = (access t (2 * k + 1 + 1))),
  forall (HW_13: result1 < result2),
  forall (HW_14: (0 <= k /\ k < (array_length t)) /\ 0 <= (2 * k + 1 + 1) /\
                 (2 * k + 1 + 1) < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_15: (exchange t0 t k (2 * k + 1 + 1))),
  forall (HW_16: (Zwf 0 (n - (2 * k + 1 + 1)) (n - k))),
  forall (HW_17: (0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) <= n) /\ n <
                 (array_length t0) /\
                 (forall (i:Z),
                  ((2 * k + 1 + 1 + 1) <= i /\ i <= n -> (heap t0 n i)))),
  forall (t1: (array Z)),
  forall (HW_18: (permut t1 t0) /\
                 (forall (i:Z),
                  ((2 * k + 1 + 1) <= i /\ i <= n -> (heap t1 n i))) /\
                 (forall (i:Z),
                  (0 <= i /\ i < (2 * k + 1 + 1) \/ (2 * k + 1 + 1) < i /\
                   i < (2 * (2 * k + 1 + 1) + 1) \/ n < i /\ i <
                   (array_length t1) -> (access t1 i) = (access t0 i))) /\
                 (forall (v:Z),
                  ((inftree t0 n v (2 * k + 1 + 1)) ->
                   (inftree t1 n v (2 * k + 1 + 1))))),
  (permut t1 t) /\ (forall (i:Z), (k <= i /\ i <= n -> (heap t1 n i))) /\
  (forall (i:Z),
   (0 <= i /\ i < k \/ k < i /\ i < (2 * k + 1) \/ n < i /\ i <
    (array_length t1) -> (access t1 i) = (access t i))) /\
  (forall (v:Z), ((inftree t n v k) -> (inftree t1 n v k))).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_10 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_8: result < result0),
  forall (HW_9: 0 <= k /\ k < (array_length t)),
  forall (result1: Z),
  forall (HW_10: result1 = (access t k)),
  forall (HW_11: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result2: Z),
  forall (HW_12: result2 = (access t (2 * k + 1 + 1))),
  forall (HW_19: result1 >= result2),
  (permut t t) /\ (forall (i:Z), (k <= i /\ i <= n -> (heap t n i))) /\
  (forall (i:Z),
   (0 <= i /\ i < k \/ k < i /\ i < (2 * k + 1) \/ n < i /\ i <
    (array_length t) -> (access t i) = (access t i))) /\
  (forall (v:Z), ((inftree t n v k) -> (inftree t n v k))).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_11 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_20: result >= result0),
  (select_son t k n (2 * k + 1)).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_12 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_20: result >= result0),
  0 <= k /\ k < (array_length t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_13 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_20: result >= result0),
  forall (HW_21: 0 <= k /\ k < (array_length t)),
  forall (result1: Z),
  forall (HW_22: result1 = (access t k)),
  0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_14 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_20: result >= result0),
  forall (HW_21: 0 <= k /\ k < (array_length t)),
  forall (result1: Z),
  forall (HW_22: result1 = (access t k)),
  forall (HW_23: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result2: Z),
  forall (HW_24: result2 = (access t (2 * k + 1))),
  forall (HW_25: result1 < result2),
  (0 <= k /\ k < (array_length t)) /\ 0 <= (2 * k + 1) /\ (2 * k + 1) <
  (array_length t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_15 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_20: result >= result0),
  forall (HW_21: 0 <= k /\ k < (array_length t)),
  forall (result1: Z),
  forall (HW_22: result1 = (access t k)),
  forall (HW_23: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result2: Z),
  forall (HW_24: result2 = (access t (2 * k + 1))),
  forall (HW_25: result1 < result2),
  forall (HW_26: (0 <= k /\ k < (array_length t)) /\ 0 <= (2 * k + 1) /\
                 (2 * k + 1) < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_27: (exchange t0 t k (2 * k + 1))),
  (Zwf 0 (n - (2 * k + 1)) (n - k)).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_16 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_20: result >= result0),
  forall (HW_21: 0 <= k /\ k < (array_length t)),
  forall (result1: Z),
  forall (HW_22: result1 = (access t k)),
  forall (HW_23: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result2: Z),
  forall (HW_24: result2 = (access t (2 * k + 1))),
  forall (HW_25: result1 < result2),
  forall (HW_26: (0 <= k /\ k < (array_length t)) /\ 0 <= (2 * k + 1) /\
                 (2 * k + 1) < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_27: (exchange t0 t k (2 * k + 1))),
  forall (HW_28: (Zwf 0 (n - (2 * k + 1)) (n - k))),
  (0 <= (2 * k + 1) /\ (2 * k + 1) <= n) /\ n < (array_length t0) /\
  (forall (i:Z), ((2 * k + 1 + 1) <= i /\ i <= n -> (heap t0 n i))).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_17 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_20: result >= result0),
  forall (HW_21: 0 <= k /\ k < (array_length t)),
  forall (result1: Z),
  forall (HW_22: result1 = (access t k)),
  forall (HW_23: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result2: Z),
  forall (HW_24: result2 = (access t (2 * k + 1))),
  forall (HW_25: result1 < result2),
  forall (HW_26: (0 <= k /\ k < (array_length t)) /\ 0 <= (2 * k + 1) /\
                 (2 * k + 1) < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_27: (exchange t0 t k (2 * k + 1))),
  forall (HW_28: (Zwf 0 (n - (2 * k + 1)) (n - k))),
  forall (HW_29: (0 <= (2 * k + 1) /\ (2 * k + 1) <= n) /\ n <
                 (array_length t0) /\
                 (forall (i:Z),
                  ((2 * k + 1 + 1) <= i /\ i <= n -> (heap t0 n i)))),
  forall (t1: (array Z)),
  forall (HW_30: (permut t1 t0) /\
                 (forall (i:Z), ((2 * k + 1) <= i /\ i <= n -> (heap t1 n i))) /\
                 (forall (i:Z),
                  (0 <= i /\ i < (2 * k + 1) \/ (2 * k + 1) < i /\ i <
                   (2 * (2 * k + 1) + 1) \/ n < i /\ i < (array_length t1) ->
                   (access t1 i) = (access t0 i))) /\
                 (forall (v:Z),
                  ((inftree t0 n v (2 * k + 1)) ->
                   (inftree t1 n v (2 * k + 1))))),
  (permut t1 t) /\ (forall (i:Z), (k <= i /\ i <= n -> (heap t1 n i))) /\
  (forall (i:Z),
   (0 <= i /\ i < k \/ k < i /\ i < (2 * k + 1) \/ n < i /\ i <
    (array_length t1) -> (access t1 i) = (access t i))) /\
  (forall (v:Z), ((inftree t n v k) -> (inftree t1 n v k))).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_18 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_3: (2 * k + 1 + 1) <= n),
  forall (HW_4: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (2 * k + 1))),
  forall (HW_6: 0 <= (2 * k + 1 + 1) /\ (2 * k + 1 + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t (2 * k + 1 + 1))),
  forall (HW_20: result >= result0),
  forall (HW_21: 0 <= k /\ k < (array_length t)),
  forall (result1: Z),
  forall (HW_22: result1 = (access t k)),
  forall (HW_23: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result2: Z),
  forall (HW_24: result2 = (access t (2 * k + 1))),
  forall (HW_31: result1 >= result2),
  (permut t t) /\ (forall (i:Z), (k <= i /\ i <= n -> (heap t n i))) /\
  (forall (i:Z),
   (0 <= i /\ i < k \/ k < i /\ i < (2 * k + 1) \/ n < i /\ i <
    (array_length t) -> (access t i) = (access t i))) /\
  (forall (v:Z), ((inftree t n v k) -> (inftree t n v k))).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_19 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_32: (2 * k + 1 + 1) > n),
  (select_son t k n (2 * k + 1)).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_20 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_32: (2 * k + 1 + 1) > n),
  0 <= k /\ k < (array_length t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_21 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_32: (2 * k + 1 + 1) > n),
  forall (HW_33: 0 <= k /\ k < (array_length t)),
  forall (result: Z),
  forall (HW_34: result = (access t k)),
  0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_22 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_32: (2 * k + 1 + 1) > n),
  forall (HW_33: 0 <= k /\ k < (array_length t)),
  forall (result: Z),
  forall (HW_34: result = (access t k)),
  forall (HW_35: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_36: result0 = (access t (2 * k + 1))),
  forall (HW_37: result < result0),
  (0 <= k /\ k < (array_length t)) /\ 0 <= (2 * k + 1) /\ (2 * k + 1) <
  (array_length t).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_23 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_32: (2 * k + 1 + 1) > n),
  forall (HW_33: 0 <= k /\ k < (array_length t)),
  forall (result: Z),
  forall (HW_34: result = (access t k)),
  forall (HW_35: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_36: result0 = (access t (2 * k + 1))),
  forall (HW_37: result < result0),
  forall (HW_38: (0 <= k /\ k < (array_length t)) /\ 0 <= (2 * k + 1) /\
                 (2 * k + 1) < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_39: (exchange t0 t k (2 * k + 1))),
  (Zwf 0 (n - (2 * k + 1)) (n - k)).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_24 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_32: (2 * k + 1 + 1) > n),
  forall (HW_33: 0 <= k /\ k < (array_length t)),
  forall (result: Z),
  forall (HW_34: result = (access t k)),
  forall (HW_35: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_36: result0 = (access t (2 * k + 1))),
  forall (HW_37: result < result0),
  forall (HW_38: (0 <= k /\ k < (array_length t)) /\ 0 <= (2 * k + 1) /\
                 (2 * k + 1) < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_39: (exchange t0 t k (2 * k + 1))),
  forall (HW_40: (Zwf 0 (n - (2 * k + 1)) (n - k))),
  (0 <= (2 * k + 1) /\ (2 * k + 1) <= n) /\ n < (array_length t0) /\
  (forall (i:Z), ((2 * k + 1 + 1) <= i /\ i <= n -> (heap t0 n i))).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_25 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_32: (2 * k + 1 + 1) > n),
  forall (HW_33: 0 <= k /\ k < (array_length t)),
  forall (result: Z),
  forall (HW_34: result = (access t k)),
  forall (HW_35: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_36: result0 = (access t (2 * k + 1))),
  forall (HW_37: result < result0),
  forall (HW_38: (0 <= k /\ k < (array_length t)) /\ 0 <= (2 * k + 1) /\
                 (2 * k + 1) < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_39: (exchange t0 t k (2 * k + 1))),
  forall (HW_40: (Zwf 0 (n - (2 * k + 1)) (n - k))),
  forall (HW_41: (0 <= (2 * k + 1) /\ (2 * k + 1) <= n) /\ n <
                 (array_length t0) /\
                 (forall (i:Z),
                  ((2 * k + 1 + 1) <= i /\ i <= n -> (heap t0 n i)))),
  forall (t1: (array Z)),
  forall (HW_42: (permut t1 t0) /\
                 (forall (i:Z), ((2 * k + 1) <= i /\ i <= n -> (heap t1 n i))) /\
                 (forall (i:Z),
                  (0 <= i /\ i < (2 * k + 1) \/ (2 * k + 1) < i /\ i <
                   (2 * (2 * k + 1) + 1) \/ n < i /\ i < (array_length t1) ->
                   (access t1 i) = (access t0 i))) /\
                 (forall (v:Z),
                  ((inftree t0 n v (2 * k + 1)) ->
                   (inftree t1 n v (2 * k + 1))))),
  (permut t1 t) /\ (forall (i:Z), (k <= i /\ i <= n -> (heap t1 n i))) /\
  (forall (i:Z),
   (0 <= i /\ i < k \/ k < i /\ i < (2 * k + 1) \/ n < i /\ i <
    (array_length t1) -> (access t1 i) = (access t i))) /\
  (forall (v:Z), ((inftree t n v k) -> (inftree t1 n v k))).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_26 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_2: (2 * k + 1) <= n),
  forall (HW_32: (2 * k + 1 + 1) > n),
  forall (HW_33: 0 <= k /\ k < (array_length t)),
  forall (result: Z),
  forall (HW_34: result = (access t k)),
  forall (HW_35: 0 <= (2 * k + 1) /\ (2 * k + 1) < (array_length t)),
  forall (result0: Z),
  forall (HW_36: result0 = (access t (2 * k + 1))),
  forall (HW_43: result >= result0),
  (permut t t) /\ (forall (i:Z), (k <= i /\ i <= n -> (heap t n i))) /\
  (forall (i:Z),
   (0 <= i /\ i < k \/ k < i /\ i < (2 * k + 1) \/ n < i /\ i <
    (array_length t) -> (access t i) = (access t i))) /\
  (forall (v:Z), ((inftree t n v k) -> (inftree t n v k))).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma downheap_po_27 : 
  forall (k: Z),
  forall (n: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= n) /\ n < (array_length t) /\
                (forall (i:Z), ((k + 1) <= i /\ i <= n -> (heap t n i)))),
  forall (HW_44: (2 * k + 1) > n),
  (permut t t) /\ (forall (i:Z), (k <= i /\ i <= n -> (heap t n i))) /\
  (forall (i:Z),
   (0 <= i /\ i < k \/ k < i /\ i < (2 * k + 1) \/ n < i /\ i <
    (array_length t) -> (access t i) = (access t i))) /\
  (forall (v:Z), ((inftree t n v k) -> (inftree t n v k))).
Proof.
(* FILL PROOF HERE *)
Save.

