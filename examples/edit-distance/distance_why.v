(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Export words.
Require Import Omega.
Require Import Sumbool.

(*Why*) Parameter n1 : Z.
Axiom n1_non_negative : (0 <= n1)%Z.

(*Why*) Parameter n2 : Z.
Axiom n2_non_negative : (0 <= n2)%Z.

Ltac Omega' :=
  generalize n1_non_negative; generalize n2_non_negative;
   abstract omega.

Definition min_suffix (w1 w2:array A) (i j n:Z) :=
  min_dist (suffix n1 w1 i) (suffix n2 w2 j) n.

Definition test_char (a b:A) := bool_of_sumbool (A_eq_dec a b).

(* Why obligation from file "distance.mlw", characters 1780-1796 *)
Lemma distance_po_1 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Pre4: Variant1 = (n2 + 1 - i1)),
  forall (Pre3: (0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                (n2 + 1) /\
                (forall (j:Z), (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))),
  forall (Test2: i1 <= n2),
  0 <= i1 /\ i1 < (array_length t0).
Proof.
simpl; intuition.
Qed.

(* Why obligation from file "distance.mlw", characters 1780-1817 *)
Lemma distance_po_2 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Pre4: Variant1 = (n2 + 1 - i1)),
  forall (Pre3: (0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                (n2 + 1) /\
                (forall (j:Z), (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))),
  forall (Test2: i1 <= n2),
  forall (Pre2: 0 <= i1 /\ i1 < (array_length t0)),
  forall (t1: (array Z)),
  forall (Post2: t1 = (store t0 i1 (n2 - i1))),
  forall (i2: Z),
  forall (Post3: i2 = (i1 + 1)),
  ((0 <= i2 /\ i2 <= (n2 + 1)) /\ (array_length t1) = (n2 + 1) /\
  (forall (j:Z), (0 <= j /\ j < i2 -> (access t1 j) = (n2 - j)))) /\
  (Zwf 0 (n2 + 1 - i2) (n2 + 1 - i1)).
Proof.
intuition.
ArraySubst t1.
subst t1.
 AccessStore i1 j Hij; try Omega'.
apply H8; Omega'.
Qed.

(* Why obligation from file "distance.mlw", characters 1645-1744 *)
Lemma distance_po_3 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  (0 <= i0 /\ i0 <= (n2 + 1)) /\ (array_length t) = (n2 + 1) /\
  (forall (j:Z), (0 <= j /\ j < i0 -> (access t j) = (n2 - j))).
Proof.
intuition.
Omega'.
Qed.

(* Why obligation from file "distance.mlw", characters 2074-2079 *)
Lemma distance_po_4 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post4: ((0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))) /\
                 i1 > n2),
  forall (i2: Z),
  forall (Post5: i2 = (n1 - 1)),
  forall (Variant3: Z),
  forall (i3: Z),
  forall (t1: (array Z)),
  forall (Pre26: Variant3 = (i3 + 1)),
  forall (Pre25: ((Zopp 1) <= i3 /\ i3 <= (n1 - 1)) /\ (array_length t1) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j <= n2 ->
                   (min_suffix w1 w2 (i3 + 1) j (access t1 j))))),
  forall (Test8: i3 >= 0),
  0 <= n2 /\ n2 < (array_length t1).
Proof.
intuition.
Omega'.
Qed.

(* Why obligation from file "distance.mlw", characters 2527-2532 *)
Lemma distance_po_5 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post4: ((0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))) /\
                 i1 > n2),
  forall (i2: Z),
  forall (Post5: i2 = (n1 - 1)),
  forall (Variant3: Z),
  forall (i3: Z),
  forall (t1: (array Z)),
  forall (Pre26: Variant3 = (i3 + 1)),
  forall (Pre25: ((Zopp 1) <= i3 /\ i3 <= (n1 - 1)) /\ (array_length t1) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j <= n2 ->
                   (min_suffix w1 w2 (i3 + 1) j (access t1 j))))),
  forall (Test8: i3 >= 0),
  forall (Pre24: 0 <= n2 /\ n2 < (array_length t1)),
  forall (old1: Z),
  forall (Post6: old1 = (access t1 n2)),
  forall (Pre22: 0 <= n2 /\ n2 < (array_length t1)),
  forall (Pre23: 0 <= n2 /\ n2 < (array_length t1)),
  forall (t2: (array Z)),
  forall (Post7: t2 = (store t1 n2 ((access t1 n2) + 1))),
  forall (j1: Z),
  forall (Post8: j1 = (n2 - 1)),
  forall (Variant5: Z),
  forall (j2: Z),
  forall (old2: Z),
  forall (t3: (array Z)),
  forall (Pre21: Variant5 = (j2 + 1)),
  forall (Pre20: ((Zopp 1) <= j2 /\ j2 <= (n2 - 1)) /\ (array_length t3) =
                 (n2 + 1) /\
                 (forall (k:Z),
                  (j2 < k /\ k <= n2 -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
                 (forall (k:Z),
                  (0 <= k /\ k <= j2 ->
                   (min_suffix w1 w2 (i3 + 1) k (access t3 k)))) /\
                 (min_suffix w1 w2 (i3 + 1) (j2 + 1) old2)),
  forall (Test7: j2 >= 0),
  forall (temp: Z),
  forall (Post12: temp = old2),
  0 <= j2 /\ j2 < (array_length t3).
Proof.
intuition.
Qed.

(* Why obligation from file "distance.mlw", characters 2553-2559 *)
Lemma distance_po_6 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post4: ((0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))) /\
                 i1 > n2),
  forall (i2: Z),
  forall (Post5: i2 = (n1 - 1)),
  forall (Variant3: Z),
  forall (i3: Z),
  forall (t1: (array Z)),
  forall (Pre26: Variant3 = (i3 + 1)),
  forall (Pre25: ((Zopp 1) <= i3 /\ i3 <= (n1 - 1)) /\ (array_length t1) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j <= n2 ->
                   (min_suffix w1 w2 (i3 + 1) j (access t1 j))))),
  forall (Test8: i3 >= 0),
  forall (Pre24: 0 <= n2 /\ n2 < (array_length t1)),
  forall (old1: Z),
  forall (Post6: old1 = (access t1 n2)),
  forall (Pre22: 0 <= n2 /\ n2 < (array_length t1)),
  forall (Pre23: 0 <= n2 /\ n2 < (array_length t1)),
  forall (t2: (array Z)),
  forall (Post7: t2 = (store t1 n2 ((access t1 n2) + 1))),
  forall (j1: Z),
  forall (Post8: j1 = (n2 - 1)),
  forall (Variant5: Z),
  forall (j2: Z),
  forall (old2: Z),
  forall (t3: (array Z)),
  forall (Pre21: Variant5 = (j2 + 1)),
  forall (Pre20: ((Zopp 1) <= j2 /\ j2 <= (n2 - 1)) /\ (array_length t3) =
                 (n2 + 1) /\
                 (forall (k:Z),
                  (j2 < k /\ k <= n2 -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
                 (forall (k:Z),
                  (0 <= k /\ k <= j2 ->
                   (min_suffix w1 w2 (i3 + 1) k (access t3 k)))) /\
                 (min_suffix w1 w2 (i3 + 1) (j2 + 1) old2)),
  forall (Test7: j2 >= 0),
  forall (temp: Z),
  forall (Post12: temp = old2),
  forall (Pre19: 0 <= j2 /\ j2 < (array_length t3)),
  forall (old3: Z),
  forall (Post9: old3 = (access t3 j2)),
  0 <= i3 /\ i3 < (array_length w1).
Proof.
intuition.
Qed.

(* Why obligation from file "distance.mlw", characters 2560-2566 *)
Lemma distance_po_7 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post4: ((0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))) /\
                 i1 > n2),
  forall (i2: Z),
  forall (Post5: i2 = (n1 - 1)),
  forall (Variant3: Z),
  forall (i3: Z),
  forall (t1: (array Z)),
  forall (Pre26: Variant3 = (i3 + 1)),
  forall (Pre25: ((Zopp 1) <= i3 /\ i3 <= (n1 - 1)) /\ (array_length t1) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j <= n2 ->
                   (min_suffix w1 w2 (i3 + 1) j (access t1 j))))),
  forall (Test8: i3 >= 0),
  forall (Pre24: 0 <= n2 /\ n2 < (array_length t1)),
  forall (old1: Z),
  forall (Post6: old1 = (access t1 n2)),
  forall (Pre22: 0 <= n2 /\ n2 < (array_length t1)),
  forall (Pre23: 0 <= n2 /\ n2 < (array_length t1)),
  forall (t2: (array Z)),
  forall (Post7: t2 = (store t1 n2 ((access t1 n2) + 1))),
  forall (j1: Z),
  forall (Post8: j1 = (n2 - 1)),
  forall (Variant5: Z),
  forall (j2: Z),
  forall (old2: Z),
  forall (t3: (array Z)),
  forall (Pre21: Variant5 = (j2 + 1)),
  forall (Pre20: ((Zopp 1) <= j2 /\ j2 <= (n2 - 1)) /\ (array_length t3) =
                 (n2 + 1) /\
                 (forall (k:Z),
                  (j2 < k /\ k <= n2 -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
                 (forall (k:Z),
                  (0 <= k /\ k <= j2 ->
                   (min_suffix w1 w2 (i3 + 1) k (access t3 k)))) /\
                 (min_suffix w1 w2 (i3 + 1) (j2 + 1) old2)),
  forall (Test7: j2 >= 0),
  forall (temp: Z),
  forall (Post12: temp = old2),
  forall (Pre19: 0 <= j2 /\ j2 < (array_length t3)),
  forall (old3: Z),
  forall (Post9: old3 = (access t3 j2)),
  forall (Pre17: 0 <= i3 /\ i3 < (array_length w1)),
  0 <= j2 /\ j2 < (array_length w2).
Proof.
intuition.
Qed.

(* Why obligation from file "distance.mlw", characters 2580-2593 *)
Lemma distance_po_8 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post4: ((0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))) /\
                 i1 > n2),
  forall (i2: Z),
  forall (Post5: i2 = (n1 - 1)),
  forall (Variant3: Z),
  forall (i3: Z),
  forall (t1: (array Z)),
  forall (Pre26: Variant3 = (i3 + 1)),
  forall (Pre25: ((Zopp 1) <= i3 /\ i3 <= (n1 - 1)) /\ (array_length t1) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j <= n2 ->
                   (min_suffix w1 w2 (i3 + 1) j (access t1 j))))),
  forall (Test8: i3 >= 0),
  forall (Pre24: 0 <= n2 /\ n2 < (array_length t1)),
  forall (old1: Z),
  forall (Post6: old1 = (access t1 n2)),
  forall (Pre22: 0 <= n2 /\ n2 < (array_length t1)),
  forall (Pre23: 0 <= n2 /\ n2 < (array_length t1)),
  forall (t2: (array Z)),
  forall (Post7: t2 = (store t1 n2 ((access t1 n2) + 1))),
  forall (j1: Z),
  forall (Post8: j1 = (n2 - 1)),
  forall (Variant5: Z),
  forall (j2: Z),
  forall (old2: Z),
  forall (t3: (array Z)),
  forall (Pre21: Variant5 = (j2 + 1)),
  forall (Pre20: ((Zopp 1) <= j2 /\ j2 <= (n2 - 1)) /\ (array_length t3) =
                 (n2 + 1) /\
                 (forall (k:Z),
                  (j2 < k /\ k <= n2 -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
                 (forall (k:Z),
                  (0 <= k /\ k <= j2 ->
                   (min_suffix w1 w2 (i3 + 1) k (access t3 k)))) /\
                 (min_suffix w1 w2 (i3 + 1) (j2 + 1) old2)),
  forall (Test7: j2 >= 0),
  forall (temp: Z),
  forall (Post12: temp = old2),
  forall (Pre19: 0 <= j2 /\ j2 < (array_length t3)),
  forall (old3: Z),
  forall (Post9: old3 = (access t3 j2)),
  forall (Pre17: 0 <= i3 /\ i3 < (array_length w1)),
  forall (Pre18: 0 <= j2 /\ j2 < (array_length w2)),
  forall (Test6: (access w1 i3) = (access w2 j2)),
  forall (Pre16: 0 <= j2 /\ j2 < (array_length t3)),
  forall (t4: (array Z)),
  forall (Post10: t4 = (store t3 j2 temp)),
  (forall (j:Z),
   (j = (j2 - 1) -> (((Zopp 1) <= j /\ j <= (n2 - 1)) /\ (array_length t4) =
    (n2 + 1) /\
    (forall (k:Z),
     (j < k /\ k <= n2 -> (min_suffix w1 w2 i3 k (access t4 k)))) /\
    (forall (k:Z),
     (0 <= k /\ k <= j -> (min_suffix w1 w2 (i3 + 1) k (access t4 k)))) /\
    (min_suffix w1 w2 (i3 + 1) (j + 1) old3)) /\ (Zwf 0 (j + 1) (j2 + 1)))).
Proof.
intuition.
ArraySubst t4.
unfold min_suffix.
subst t4.
AccessStore j2 k Hj2k.
  (* j2=k *)
  rewrite (suffix_is_cons n1 w1 i3); [ idtac | Omega' ].
  rewrite (suffix_is_cons n2 w2 k); [ idtac | Omega' ].
  rewrite Test6.
 rewrite <- Hj2k.
  apply min_dist_equal.
  subst temp; assumption.
  Omega'.
  (* j2<>k *)
  unfold min_suffix in H16.
  apply H18; Omega'.
  Omega'.
  Omega'.
unfold min_suffix.
subst t4.
AccessOther.
unfold min_suffix in H21; apply H21; Omega'.
replace (j + 1)%Z with j2; [ idtac | Omega' ].
subst old3.
unfold min_suffix; unfold min_suffix in H21; apply H21; Omega'.
Qed.

(* Why obligation from file "distance.mlw", characters 2632-2639 *)
Lemma distance_po_9 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post4: ((0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))) /\
                 i1 > n2),
  forall (i2: Z),
  forall (Post5: i2 = (n1 - 1)),
  forall (Variant3: Z),
  forall (i3: Z),
  forall (t1: (array Z)),
  forall (Pre26: Variant3 = (i3 + 1)),
  forall (Pre25: ((Zopp 1) <= i3 /\ i3 <= (n1 - 1)) /\ (array_length t1) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j <= n2 ->
                   (min_suffix w1 w2 (i3 + 1) j (access t1 j))))),
  forall (Test8: i3 >= 0),
  forall (Pre24: 0 <= n2 /\ n2 < (array_length t1)),
  forall (old1: Z),
  forall (Post6: old1 = (access t1 n2)),
  forall (Pre22: 0 <= n2 /\ n2 < (array_length t1)),
  forall (Pre23: 0 <= n2 /\ n2 < (array_length t1)),
  forall (t2: (array Z)),
  forall (Post7: t2 = (store t1 n2 ((access t1 n2) + 1))),
  forall (j1: Z),
  forall (Post8: j1 = (n2 - 1)),
  forall (Variant5: Z),
  forall (j2: Z),
  forall (old2: Z),
  forall (t3: (array Z)),
  forall (Pre21: Variant5 = (j2 + 1)),
  forall (Pre20: ((Zopp 1) <= j2 /\ j2 <= (n2 - 1)) /\ (array_length t3) =
                 (n2 + 1) /\
                 (forall (k:Z),
                  (j2 < k /\ k <= n2 -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
                 (forall (k:Z),
                  (0 <= k /\ k <= j2 ->
                   (min_suffix w1 w2 (i3 + 1) k (access t3 k)))) /\
                 (min_suffix w1 w2 (i3 + 1) (j2 + 1) old2)),
  forall (Test7: j2 >= 0),
  forall (temp: Z),
  forall (Post12: temp = old2),
  forall (Pre19: 0 <= j2 /\ j2 < (array_length t3)),
  forall (old3: Z),
  forall (Post9: old3 = (access t3 j2)),
  forall (Pre17: 0 <= i3 /\ i3 < (array_length w1)),
  forall (Pre18: 0 <= j2 /\ j2 < (array_length w2)),
  forall (Test5: ~(access w1 i3) = (access w2 j2)),
  forall (Pre13: 0 <= j2 /\ j2 < (array_length t3)),
  0 <= (j2 + 1) /\ (j2 + 1) < (array_length t3).
Proof.
intuition.
Qed.

(* Why obligation from file "distance.mlw", characters 2611-2644 *)
Lemma distance_po_10 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post4: ((0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))) /\
                 i1 > n2),
  forall (i2: Z),
  forall (Post5: i2 = (n1 - 1)),
  forall (Variant3: Z),
  forall (i3: Z),
  forall (t1: (array Z)),
  forall (Pre26: Variant3 = (i3 + 1)),
  forall (Pre25: ((Zopp 1) <= i3 /\ i3 <= (n1 - 1)) /\ (array_length t1) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j <= n2 ->
                   (min_suffix w1 w2 (i3 + 1) j (access t1 j))))),
  forall (Test8: i3 >= 0),
  forall (Pre24: 0 <= n2 /\ n2 < (array_length t1)),
  forall (old1: Z),
  forall (Post6: old1 = (access t1 n2)),
  forall (Pre22: 0 <= n2 /\ n2 < (array_length t1)),
  forall (Pre23: 0 <= n2 /\ n2 < (array_length t1)),
  forall (t2: (array Z)),
  forall (Post7: t2 = (store t1 n2 ((access t1 n2) + 1))),
  forall (j1: Z),
  forall (Post8: j1 = (n2 - 1)),
  forall (Variant5: Z),
  forall (j2: Z),
  forall (old2: Z),
  forall (t3: (array Z)),
  forall (Pre21: Variant5 = (j2 + 1)),
  forall (Pre20: ((Zopp 1) <= j2 /\ j2 <= (n2 - 1)) /\ (array_length t3) =
                 (n2 + 1) /\
                 (forall (k:Z),
                  (j2 < k /\ k <= n2 -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
                 (forall (k:Z),
                  (0 <= k /\ k <= j2 ->
                   (min_suffix w1 w2 (i3 + 1) k (access t3 k)))) /\
                 (min_suffix w1 w2 (i3 + 1) (j2 + 1) old2)),
  forall (Test7: j2 >= 0),
  forall (temp: Z),
  forall (Post12: temp = old2),
  forall (Pre19: 0 <= j2 /\ j2 < (array_length t3)),
  forall (old3: Z),
  forall (Post9: old3 = (access t3 j2)),
  forall (Pre17: 0 <= i3 /\ i3 < (array_length w1)),
  forall (Pre18: 0 <= j2 /\ j2 < (array_length w2)),
  forall (Test5: ~(access w1 i3) = (access w2 j2)),
  forall (Pre13: 0 <= j2 /\ j2 < (array_length t3)),
  forall (Pre14: 0 <= (j2 + 1) /\ (j2 + 1) < (array_length t3)),
  forall (Pre15: 0 <= j2 /\ j2 < (array_length t3)),
  forall (t4: (array Z)),
  forall (Post11: t4 = (store t3 j2
                        ((Zmin (access t3 j2) (access t3 (j2 + 1))) + 1))),
  (forall (j:Z),
   (j = (j2 - 1) -> (((Zopp 1) <= j /\ j <= (n2 - 1)) /\ (array_length t4) =
    (n2 + 1) /\
    (forall (k:Z),
     (j < k /\ k <= n2 -> (min_suffix w1 w2 i3 k (access t4 k)))) /\
    (forall (k:Z),
     (0 <= k /\ k <= j -> (min_suffix w1 w2 (i3 + 1) k (access t4 k)))) /\
    (min_suffix w1 w2 (i3 + 1) (j + 1) old3)) /\ (Zwf 0 (j + 1) (j2 + 1)))).
Proof.
intuition.
ArraySubst t4.
unfold min_suffix.
rewrite Post11; clear Post11.
AccessStore j2 k Hj2k.
  (* j2=k *)
  rewrite <- Hj2k.
    rewrite (suffix_is_cons n1 w1 i3); [ idtac | Omega' ].
  rewrite (suffix_is_cons n2 w2 j2); [ idtac | Omega' ].
  apply min_dist_diff.
   assumption.
  rewrite <- (suffix_is_cons n1 w1 i3); [ idtac | Omega' ].
  apply H18; Omega'.
  rewrite <- (suffix_is_cons n2 w2 j2); [ idtac | Omega' ].
  apply H21; Omega'.
  Omega'.
  (* j2<> k *)
  apply H18; Omega'.
  Omega'.
  Omega'.
rewrite Post11; clear Post11.
unfold min_suffix.
AccessOther.
apply H21; Omega'.
replace (j + 1)%Z with j2; [ idtac | Omega' ].
subst old3; apply H21; Omega'.
Qed.

(* Why obligation from file "distance.mlw", characters 2202-2450 *)
Lemma distance_po_11 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post4: ((0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))) /\
                 i1 > n2),
  forall (i2: Z),
  forall (Post5: i2 = (n1 - 1)),
  forall (Variant3: Z),
  forall (i3: Z),
  forall (t1: (array Z)),
  forall (Pre26: Variant3 = (i3 + 1)),
  forall (Pre25: ((Zopp 1) <= i3 /\ i3 <= (n1 - 1)) /\ (array_length t1) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j <= n2 ->
                   (min_suffix w1 w2 (i3 + 1) j (access t1 j))))),
  forall (Test8: i3 >= 0),
  forall (Pre24: 0 <= n2 /\ n2 < (array_length t1)),
  forall (old1: Z),
  forall (Post6: old1 = (access t1 n2)),
  forall (Pre22: 0 <= n2 /\ n2 < (array_length t1)),
  forall (Pre23: 0 <= n2 /\ n2 < (array_length t1)),
  forall (t2: (array Z)),
  forall (Post7: t2 = (store t1 n2 ((access t1 n2) + 1))),
  forall (j1: Z),
  forall (Post8: j1 = (n2 - 1)),
  ((Zopp 1) <= j1 /\ j1 <= (n2 - 1)) /\ (array_length t2) = (n2 + 1) /\
  (forall (k:Z), (j1 < k /\ k <= n2 -> (min_suffix w1 w2 i3 k (access t2 k)))) /\
  (forall (k:Z),
   (0 <= k /\ k <= j1 -> (min_suffix w1 w2 (i3 + 1) k (access t2 k)))) /\
  (min_suffix w1 w2 (i3 + 1) (j1 + 1) old1).
Proof.
intuition.
ArraySubst t2.
rewrite Post7; clear Post7.
replace k with n2; [ idtac | Omega' ].
unfold min_suffix.
rewrite (suffix_is_cons n1 w1 i3).
rewrite suffix_n_is_eps.
AccessSame.
apply min_dist_eps.
rewrite <- suffix_n_is_eps with (n := n2) (t := w2).
apply H13; Omega'.
Omega'.
rewrite Post7.
AccessOther.
apply H13; Omega'.
rewrite Post6.
replace n2 with (j1 + 1)%Z; [ idtac | Omega' ].
apply H13; Omega'.
Qed.

(* Why obligation from file "distance.mlw", characters 2067-2709 *)
Lemma distance_po_12 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post4: ((0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))) /\
                 i1 > n2),
  forall (i2: Z),
  forall (Post5: i2 = (n1 - 1)),
  forall (Variant3: Z),
  forall (i3: Z),
  forall (t1: (array Z)),
  forall (Pre26: Variant3 = (i3 + 1)),
  forall (Pre25: ((Zopp 1) <= i3 /\ i3 <= (n1 - 1)) /\ (array_length t1) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j <= n2 ->
                   (min_suffix w1 w2 (i3 + 1) j (access t1 j))))),
  forall (Test8: i3 >= 0),
  forall (Pre24: 0 <= n2 /\ n2 < (array_length t1)),
  forall (old1: Z),
  forall (Post6: old1 = (access t1 n2)),
  forall (Pre22: 0 <= n2 /\ n2 < (array_length t1)),
  forall (Pre23: 0 <= n2 /\ n2 < (array_length t1)),
  forall (t2: (array Z)),
  forall (Post7: t2 = (store t1 n2 ((access t1 n2) + 1))),
  forall (j1: Z),
  forall (Post8: j1 = (n2 - 1)),
  forall (j2: Z),
  forall (old2: Z),
  forall (t3: (array Z)),
  forall (Post14: (((Zopp 1) <= j2 /\ j2 <= (n2 - 1)) /\ (array_length t3) =
                  (n2 + 1) /\
                  (forall (k:Z),
                   (j2 < k /\ k <= n2 ->
                    (min_suffix w1 w2 i3 k (access t3 k)))) /\
                  (forall (k:Z),
                   (0 <= k /\ k <= j2 ->
                    (min_suffix w1 w2 (i3 + 1) k (access t3 k)))) /\
                  (min_suffix w1 w2 (i3 + 1) (j2 + 1) old2)) /\ j2 < 0),
  forall (i4: Z),
  forall (Post15: i4 = (i3 - 1)),
  (((Zopp 1) <= i4 /\ i4 <= (n1 - 1)) /\ (array_length t3) = (n2 + 1) /\
  (forall (j:Z),
   (0 <= j /\ j <= n2 -> (min_suffix w1 w2 (i4 + 1) j (access t3 j))))) /\
  (Zwf 0 (i4 + 1) (i3 + 1)).
Proof.
intuition.
replace (i4 + 1)%Z with i3; [ idtac | Omega' ].
apply H20; Omega'.
Qed.

(* Why obligation from file "distance.mlw", characters 1915-2034 *)
Lemma distance_po_13 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post4: ((0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))) /\
                 i1 > n2),
  forall (i2: Z),
  forall (Post5: i2 = (n1 - 1)),
  ((Zopp 1) <= i2 /\ i2 <= (n1 - 1)) /\ (array_length t0) = (n2 + 1) /\
  (forall (j:Z),
   (0 <= j /\ j <= n2 -> (min_suffix w1 w2 (i2 + 1) j (access t0 j)))).
Proof.
intuition.
Omega'.
replace (i2 + 1)%Z with n1; [ idtac | Omega' ].
unfold min_suffix.
rewrite suffix_n_is_eps.
replace (access t0 j) with (Zlength (suffix n2 w2 j)).
exact (min_dist_eps_length (suffix n2 w2 j)).
rewrite H7.
apply suffix_length; Omega'.
Omega'.
Qed.

(* Why obligation from file "distance.mlw", characters 2728-2732 *)
Lemma distance_po_14 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post4: ((0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))) /\
                 i1 > n2),
  forall (i2: Z),
  forall (Post5: i2 = (n1 - 1)),
  forall (i3: Z),
  forall (t1: (array Z)),
  forall (Post16: (((Zopp 1) <= i3 /\ i3 <= (n1 - 1)) /\ (array_length t1) =
                  (n2 + 1) /\
                  (forall (j:Z),
                   (0 <= j /\ j <= n2 ->
                    (min_suffix w1 w2 (i3 + 1) j (access t1 j))))) /\
                  i3 < 0),
  0 <= 0 /\ 0 < (array_length t1).
Proof.
intuition.
Omega'.
Qed.


(* Why obligation from file "distance.mlw", characters 2728-2732 *)
Lemma distance_po_15 : 
  forall (t: (array Z)),
  forall (w1: (array A)),
  forall (w2: (array A)),
  forall (Pre28: (array_length w1) = n1 /\ (array_length w2) = n2 /\
                 (array_length t) = (n2 + 1)),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (t0: (array Z)),
  forall (Post4: ((0 <= i1 /\ i1 <= (n2 + 1)) /\ (array_length t0) =
                 (n2 + 1) /\
                 (forall (j:Z),
                  (0 <= j /\ j < i1 -> (access t0 j) = (n2 - j)))) /\
                 i1 > n2),
  forall (i2: Z),
  forall (Post5: i2 = (n1 - 1)),
  forall (i3: Z),
  forall (t1: (array Z)),
  forall (Post16: (((Zopp 1) <= i3 /\ i3 <= (n1 - 1)) /\ (array_length t1) =
                  (n2 + 1) /\
                  (forall (j:Z),
                   (0 <= j /\ j <= n2 ->
                    (min_suffix w1 w2 (i3 + 1) j (access t1 j))))) /\
                  i3 < 0),
  forall (Pre27: 0 <= 0 /\ 0 < (array_length t1)),
  (min_dist (word_of_array n1 w1) (word_of_array n2 w2) (access t1 0)).
Proof.
intuition.
cut ((i3 + 1)%Z = 0%Z); [ intro Hi3 | Omega' ].
rewrite Hi3 in H14.
unfold word_of_array.
unfold min_suffix in H14.
apply (H14 0%Z); Omega'.
Qed.

