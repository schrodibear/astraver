(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Export words.
Require Omega.
Require Sumbool.

(*Why*) Parameter n1 : Z.
Axiom n1_non_negative : `0 <= n1`.

(*Why*) Parameter n2 : Z.
Axiom n2_non_negative : `0 <= n2`.

Tactic Definition Omega' := 
  Generalize n1_non_negative; 
  Generalize n2_non_negative; 
  Abstract Omega.

Definition min_suffix :=
  [w1:(array A)][w2:(array A)][i,j,n:Z]
  (min_dist (suffix n1 w1 i) (suffix n2 w2 j) n).

Definition test_char := [a,b:A](bool_of_sumbool (A_eq_dec a b)).

(* Why obligation from file "distance.mlw", characters 1733-1749 *)
Lemma distance_po_1 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (Variant1: Z)
  (i1: Z)
  (t0: (array Z))
  (Pre4: Variant1 = `n2 + 1 - i1`)
  (Pre3: (`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
         ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`)))
  (Test2: `i1 <= n2`)
  `0 <= i1` /\ `i1 < (array_length t0)`.
Proof.
Simpl; Intuition.
Save.

(* Why obligation from file "distance.mlw", characters 1560-1781 *)
Lemma distance_po_2 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (Variant1: Z)
  (i1: Z)
  (t0: (array Z))
  (Pre4: Variant1 = `n2 + 1 - i1`)
  (Pre3: (`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
         ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`)))
  (Test2: `i1 <= n2`)
  (Pre2: `0 <= i1` /\ `i1 < (array_length t0)`)
  (t1: (array Z))
  (Post2: t1 = (store t0 i1 `n2 - i1`))
  (i2: Z)
  (Post3: i2 = `i1 + 1`)
  ((`0 <= i2` /\ `i2 <= n2 + 1`) /\ `(array_length t1) = n2 + 1` /\
  ((j:Z) (`0 <= j` /\ `j < i2` -> `(access t1 j) = n2 - j`))) /\
  (Zwf `0` `n2 + 1 - i2` `n2 + 1 - i1`).
Proof.
Intuition.
ArraySubst t1.
Subst t1. AccessStore i1 j Hij; Try Omega'.
Apply H8; Omega'.
Unfold Zwf; Omega'.
Save.

(* Why obligation from file "distance.mlw", characters 1598-1697 *)
Lemma distance_po_3 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (`0 <= i0` /\ `i0 <= n2 + 1`) /\ `(array_length t) = n2 + 1` /\
  ((j:Z) (`0 <= j` /\ `j < i0` -> `(access t j) = n2 - j`)).
Proof.
Intuition.
Omega'.
Save.

(* Why obligation from file "distance.mlw", characters 2027-2032 *)
Lemma distance_po_4 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post4: ((`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
          ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`))) /\
          `i1 > n2`)
  (i2: Z)
  (Post5: i2 = `n1 - 1`)
  (Variant3: Z)
  (i3: Z)
  (t1: (array Z))
  (Pre26: Variant3 = `i3 + 1`)
  (Pre25: (`(-1) <= i3` /\ `i3 <= n1 - 1`) /\ `(array_length t1) = n2 + 1` /\
          ((j:Z)
           (`0 <= j` /\ `j <= n2` ->
            (min_suffix w1 w2 `i3 + 1` j (access t1 j)))))
  (Test8: `i3 >= 0`)
  `0 <= n2` /\ `n2 < (array_length t1)`.
Proof.
Intuition.
Omega'.
Save.

(* Why obligation from file "distance.mlw", characters 2480-2485 *)
Lemma distance_po_5 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post4: ((`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
          ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`))) /\
          `i1 > n2`)
  (i2: Z)
  (Post5: i2 = `n1 - 1`)
  (Variant3: Z)
  (i3: Z)
  (t1: (array Z))
  (Pre26: Variant3 = `i3 + 1`)
  (Pre25: (`(-1) <= i3` /\ `i3 <= n1 - 1`) /\ `(array_length t1) = n2 + 1` /\
          ((j:Z)
           (`0 <= j` /\ `j <= n2` ->
            (min_suffix w1 w2 `i3 + 1` j (access t1 j)))))
  (Test8: `i3 >= 0`)
  (Pre24: `0 <= n2` /\ `n2 < (array_length t1)`)
  (old1: Z)
  (Post6: old1 = (access t1 n2))
  (Pre22: `0 <= n2` /\ `n2 < (array_length t1)`)
  (Pre23: `0 <= n2` /\ `n2 < (array_length t1)`)
  (t2: (array Z))
  (Post7: t2 = (store t1 n2 `(access t1 n2) + 1`))
  (j1: Z)
  (Post8: j1 = `n2 - 1`)
  (Variant5: Z)
  (j2: Z)
  (old2: Z)
  (t3: (array Z))
  (Pre21: Variant5 = `j2 + 1`)
  (Pre20: (`(-1) <= j2` /\ `j2 <= n2 - 1`) /\ `(array_length t3) = n2 + 1` /\
          ((k:Z)
           (`j2 < k` /\ `k <= n2` -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
          ((k:Z)
           (`0 <= k` /\ `k <= j2` ->
            (min_suffix w1 w2 `i3 + 1` k (access t3 k)))) /\
          (min_suffix w1 w2 `i3 + 1` `j2 + 1` old2))
  (Test7: `j2 >= 0`)
  (temp: Z)
  (Post12: temp = old2)
  `0 <= j2` /\ `j2 < (array_length t3)`.
Proof.
Intuition.
Save.

(* Why obligation from file "distance.mlw", characters 2506-2512 *)
Lemma distance_po_6 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post4: ((`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
          ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`))) /\
          `i1 > n2`)
  (i2: Z)
  (Post5: i2 = `n1 - 1`)
  (Variant3: Z)
  (i3: Z)
  (t1: (array Z))
  (Pre26: Variant3 = `i3 + 1`)
  (Pre25: (`(-1) <= i3` /\ `i3 <= n1 - 1`) /\ `(array_length t1) = n2 + 1` /\
          ((j:Z)
           (`0 <= j` /\ `j <= n2` ->
            (min_suffix w1 w2 `i3 + 1` j (access t1 j)))))
  (Test8: `i3 >= 0`)
  (Pre24: `0 <= n2` /\ `n2 < (array_length t1)`)
  (old1: Z)
  (Post6: old1 = (access t1 n2))
  (Pre22: `0 <= n2` /\ `n2 < (array_length t1)`)
  (Pre23: `0 <= n2` /\ `n2 < (array_length t1)`)
  (t2: (array Z))
  (Post7: t2 = (store t1 n2 `(access t1 n2) + 1`))
  (j1: Z)
  (Post8: j1 = `n2 - 1`)
  (Variant5: Z)
  (j2: Z)
  (old2: Z)
  (t3: (array Z))
  (Pre21: Variant5 = `j2 + 1`)
  (Pre20: (`(-1) <= j2` /\ `j2 <= n2 - 1`) /\ `(array_length t3) = n2 + 1` /\
          ((k:Z)
           (`j2 < k` /\ `k <= n2` -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
          ((k:Z)
           (`0 <= k` /\ `k <= j2` ->
            (min_suffix w1 w2 `i3 + 1` k (access t3 k)))) /\
          (min_suffix w1 w2 `i3 + 1` `j2 + 1` old2))
  (Test7: `j2 >= 0`)
  (temp: Z)
  (Post12: temp = old2)
  (Pre19: `0 <= j2` /\ `j2 < (array_length t3)`)
  (old3: Z)
  (Post9: old3 = (access t3 j2))
  `0 <= i3` /\ `i3 < (array_length w1)`.
Proof.
Intuition.
Save.

(* Why obligation from file "distance.mlw", characters 2513-2519 *)
Lemma distance_po_7 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post4: ((`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
          ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`))) /\
          `i1 > n2`)
  (i2: Z)
  (Post5: i2 = `n1 - 1`)
  (Variant3: Z)
  (i3: Z)
  (t1: (array Z))
  (Pre26: Variant3 = `i3 + 1`)
  (Pre25: (`(-1) <= i3` /\ `i3 <= n1 - 1`) /\ `(array_length t1) = n2 + 1` /\
          ((j:Z)
           (`0 <= j` /\ `j <= n2` ->
            (min_suffix w1 w2 `i3 + 1` j (access t1 j)))))
  (Test8: `i3 >= 0`)
  (Pre24: `0 <= n2` /\ `n2 < (array_length t1)`)
  (old1: Z)
  (Post6: old1 = (access t1 n2))
  (Pre22: `0 <= n2` /\ `n2 < (array_length t1)`)
  (Pre23: `0 <= n2` /\ `n2 < (array_length t1)`)
  (t2: (array Z))
  (Post7: t2 = (store t1 n2 `(access t1 n2) + 1`))
  (j1: Z)
  (Post8: j1 = `n2 - 1`)
  (Variant5: Z)
  (j2: Z)
  (old2: Z)
  (t3: (array Z))
  (Pre21: Variant5 = `j2 + 1`)
  (Pre20: (`(-1) <= j2` /\ `j2 <= n2 - 1`) /\ `(array_length t3) = n2 + 1` /\
          ((k:Z)
           (`j2 < k` /\ `k <= n2` -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
          ((k:Z)
           (`0 <= k` /\ `k <= j2` ->
            (min_suffix w1 w2 `i3 + 1` k (access t3 k)))) /\
          (min_suffix w1 w2 `i3 + 1` `j2 + 1` old2))
  (Test7: `j2 >= 0`)
  (temp: Z)
  (Post12: temp = old2)
  (Pre19: `0 <= j2` /\ `j2 < (array_length t3)`)
  (old3: Z)
  (Post9: old3 = (access t3 j2))
  (Pre17: `0 <= i3` /\ `i3 < (array_length w1)`)
  `0 <= j2` /\ `j2 < (array_length w2)`.
Proof.
Intuition.
Save.

(* Why obligation from file "distance.mlw", characters 2533-2546 *)
Lemma distance_po_8 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post4: ((`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
          ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`))) /\
          `i1 > n2`)
  (i2: Z)
  (Post5: i2 = `n1 - 1`)
  (Variant3: Z)
  (i3: Z)
  (t1: (array Z))
  (Pre26: Variant3 = `i3 + 1`)
  (Pre25: (`(-1) <= i3` /\ `i3 <= n1 - 1`) /\ `(array_length t1) = n2 + 1` /\
          ((j:Z)
           (`0 <= j` /\ `j <= n2` ->
            (min_suffix w1 w2 `i3 + 1` j (access t1 j)))))
  (Test8: `i3 >= 0`)
  (Pre24: `0 <= n2` /\ `n2 < (array_length t1)`)
  (old1: Z)
  (Post6: old1 = (access t1 n2))
  (Pre22: `0 <= n2` /\ `n2 < (array_length t1)`)
  (Pre23: `0 <= n2` /\ `n2 < (array_length t1)`)
  (t2: (array Z))
  (Post7: t2 = (store t1 n2 `(access t1 n2) + 1`))
  (j1: Z)
  (Post8: j1 = `n2 - 1`)
  (Variant5: Z)
  (j2: Z)
  (old2: Z)
  (t3: (array Z))
  (Pre21: Variant5 = `j2 + 1`)
  (Pre20: (`(-1) <= j2` /\ `j2 <= n2 - 1`) /\ `(array_length t3) = n2 + 1` /\
          ((k:Z)
           (`j2 < k` /\ `k <= n2` -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
          ((k:Z)
           (`0 <= k` /\ `k <= j2` ->
            (min_suffix w1 w2 `i3 + 1` k (access t3 k)))) /\
          (min_suffix w1 w2 `i3 + 1` `j2 + 1` old2))
  (Test7: `j2 >= 0`)
  (temp: Z)
  (Post12: temp = old2)
  (Pre19: `0 <= j2` /\ `j2 < (array_length t3)`)
  (old3: Z)
  (Post9: old3 = (access t3 j2))
  (Pre17: `0 <= i3` /\ `i3 < (array_length w1)`)
  (Pre18: `0 <= j2` /\ `j2 < (array_length w2)`)
  (Test6: (access w1 i3) = (access w2 j2))
  (Pre16: `0 <= j2` /\ `j2 < (array_length t3)`)
  (t4: (array Z))
  (Post10: t4 = (store t3 j2 temp))
  ((j:Z)
   (j = `j2 - 1` -> ((`(-1) <= j` /\ `j <= n2 - 1`) /\
    `(array_length t4) = n2 + 1` /\
    ((k:Z) (`j < k` /\ `k <= n2` -> (min_suffix w1 w2 i3 k (access t4 k)))) /\
    ((k:Z)
     (`0 <= k` /\ `k <= j` -> (min_suffix w1 w2 `i3 + 1` k (access t4 k)))) /\
    (min_suffix w1 w2 `i3 + 1` `j + 1` old3)) /\ (Zwf `0` `j + 1` `j2 + 1`))).
Proof.
Intuition.
ArraySubst t4.
Unfold min_suffix.
Subst t4.
AccessStore j2 k Hj2k.
  (* j2=k *)
  Rewrite (suffix_is_cons n1 w1 i3); [ Idtac | Omega' ].
  Rewrite (suffix_is_cons n2 w2 k); [ Idtac | Omega' ].
  Rewrite Test6. Rewrite <- Hj2k.
  Apply min_dist_equal.
  Subst temp; Assumption.
  Omega'.
  (* j2<>k *)
  Unfold min_suffix in H16.
  Apply H18; Omega'.
  Omega'.
  Omega'.
Unfold min_suffix.
Subst t4.
AccessOther.
Unfold min_suffix in H21; Apply H21; Omega'.
Replace `j+1` with j2; [ Idtac | Omega' ].
Subst old3.
Unfold min_suffix; Unfold min_suffix in H21; Apply H21; Omega'.
Unfold Zwf; Omega'.
Save.

(* Why obligation from file "distance.mlw", characters 2585-2592 *)
Lemma distance_po_9 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post4: ((`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
          ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`))) /\
          `i1 > n2`)
  (i2: Z)
  (Post5: i2 = `n1 - 1`)
  (Variant3: Z)
  (i3: Z)
  (t1: (array Z))
  (Pre26: Variant3 = `i3 + 1`)
  (Pre25: (`(-1) <= i3` /\ `i3 <= n1 - 1`) /\ `(array_length t1) = n2 + 1` /\
          ((j:Z)
           (`0 <= j` /\ `j <= n2` ->
            (min_suffix w1 w2 `i3 + 1` j (access t1 j)))))
  (Test8: `i3 >= 0`)
  (Pre24: `0 <= n2` /\ `n2 < (array_length t1)`)
  (old1: Z)
  (Post6: old1 = (access t1 n2))
  (Pre22: `0 <= n2` /\ `n2 < (array_length t1)`)
  (Pre23: `0 <= n2` /\ `n2 < (array_length t1)`)
  (t2: (array Z))
  (Post7: t2 = (store t1 n2 `(access t1 n2) + 1`))
  (j1: Z)
  (Post8: j1 = `n2 - 1`)
  (Variant5: Z)
  (j2: Z)
  (old2: Z)
  (t3: (array Z))
  (Pre21: Variant5 = `j2 + 1`)
  (Pre20: (`(-1) <= j2` /\ `j2 <= n2 - 1`) /\ `(array_length t3) = n2 + 1` /\
          ((k:Z)
           (`j2 < k` /\ `k <= n2` -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
          ((k:Z)
           (`0 <= k` /\ `k <= j2` ->
            (min_suffix w1 w2 `i3 + 1` k (access t3 k)))) /\
          (min_suffix w1 w2 `i3 + 1` `j2 + 1` old2))
  (Test7: `j2 >= 0`)
  (temp: Z)
  (Post12: temp = old2)
  (Pre19: `0 <= j2` /\ `j2 < (array_length t3)`)
  (old3: Z)
  (Post9: old3 = (access t3 j2))
  (Pre17: `0 <= i3` /\ `i3 < (array_length w1)`)
  (Pre18: `0 <= j2` /\ `j2 < (array_length w2)`)
  (Test5: ~(access w1 i3) = (access w2 j2))
  (Pre13: `0 <= j2` /\ `j2 < (array_length t3)`)
  `0 <= j2 + 1` /\ `j2 + 1 < (array_length t3)`.
Proof.
Intuition.
Save.

(* Why obligation from file "distance.mlw", characters 2564-2597 *)
Lemma distance_po_10 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post4: ((`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
          ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`))) /\
          `i1 > n2`)
  (i2: Z)
  (Post5: i2 = `n1 - 1`)
  (Variant3: Z)
  (i3: Z)
  (t1: (array Z))
  (Pre26: Variant3 = `i3 + 1`)
  (Pre25: (`(-1) <= i3` /\ `i3 <= n1 - 1`) /\ `(array_length t1) = n2 + 1` /\
          ((j:Z)
           (`0 <= j` /\ `j <= n2` ->
            (min_suffix w1 w2 `i3 + 1` j (access t1 j)))))
  (Test8: `i3 >= 0`)
  (Pre24: `0 <= n2` /\ `n2 < (array_length t1)`)
  (old1: Z)
  (Post6: old1 = (access t1 n2))
  (Pre22: `0 <= n2` /\ `n2 < (array_length t1)`)
  (Pre23: `0 <= n2` /\ `n2 < (array_length t1)`)
  (t2: (array Z))
  (Post7: t2 = (store t1 n2 `(access t1 n2) + 1`))
  (j1: Z)
  (Post8: j1 = `n2 - 1`)
  (Variant5: Z)
  (j2: Z)
  (old2: Z)
  (t3: (array Z))
  (Pre21: Variant5 = `j2 + 1`)
  (Pre20: (`(-1) <= j2` /\ `j2 <= n2 - 1`) /\ `(array_length t3) = n2 + 1` /\
          ((k:Z)
           (`j2 < k` /\ `k <= n2` -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
          ((k:Z)
           (`0 <= k` /\ `k <= j2` ->
            (min_suffix w1 w2 `i3 + 1` k (access t3 k)))) /\
          (min_suffix w1 w2 `i3 + 1` `j2 + 1` old2))
  (Test7: `j2 >= 0`)
  (temp: Z)
  (Post12: temp = old2)
  (Pre19: `0 <= j2` /\ `j2 < (array_length t3)`)
  (old3: Z)
  (Post9: old3 = (access t3 j2))
  (Pre17: `0 <= i3` /\ `i3 < (array_length w1)`)
  (Pre18: `0 <= j2` /\ `j2 < (array_length w2)`)
  (Test5: ~(access w1 i3) = (access w2 j2))
  (Pre13: `0 <= j2` /\ `j2 < (array_length t3)`)
  (Pre14: `0 <= j2 + 1` /\ `j2 + 1 < (array_length t3)`)
  (Pre15: `0 <= j2` /\ `j2 < (array_length t3)`)
  (t4: (array Z))
  (Post11: t4 = (store t3 j2 `(Zmin (access t3 j2) (access t3 j2 + 1)) + 1`))
  ((j:Z)
   (j = `j2 - 1` -> ((`(-1) <= j` /\ `j <= n2 - 1`) /\
    `(array_length t4) = n2 + 1` /\
    ((k:Z) (`j < k` /\ `k <= n2` -> (min_suffix w1 w2 i3 k (access t4 k)))) /\
    ((k:Z)
     (`0 <= k` /\ `k <= j` -> (min_suffix w1 w2 `i3 + 1` k (access t4 k)))) /\
    (min_suffix w1 w2 `i3 + 1` `j + 1` old3)) /\ (Zwf `0` `j + 1` `j2 + 1`))).
Proof.
Intuition.
ArraySubst t4.
Unfold min_suffix.
Rewrite Post11; Clear Post11.
AccessStore j2 k Hj2k.
  (* j2=k *)
  Rewrite <- Hj2k.  
  Rewrite (suffix_is_cons n1 w1 i3); [ Idtac | Omega' ].
  Rewrite (suffix_is_cons n2 w2 j2); [ Idtac | Omega' ].
  Apply min_dist_diff. 
  Assumption.
  Rewrite <- (suffix_is_cons n1 w1 i3); [ Idtac | Omega' ].
  Apply H18; Omega'.
  Rewrite <- (suffix_is_cons n2 w2 j2); [ Idtac | Omega' ].
  Apply H21; Omega'.
  Omega'.
  (* j2<> k *)
  Apply H18; Omega'.
  Omega'.
  Omega'.
Rewrite Post11; Clear Post11.
Unfold min_suffix.
AccessOther.
Apply H21; Omega'.
Replace `j+1` with j2; [ Idtac | Omega' ].
Subst old3; Apply H21; Omega'.
Unfold Zwf; Omega'.
Save.

(* Why obligation from file "distance.mlw", characters 2155-2403 *)
Lemma distance_po_11 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post4: ((`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
          ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`))) /\
          `i1 > n2`)
  (i2: Z)
  (Post5: i2 = `n1 - 1`)
  (Variant3: Z)
  (i3: Z)
  (t1: (array Z))
  (Pre26: Variant3 = `i3 + 1`)
  (Pre25: (`(-1) <= i3` /\ `i3 <= n1 - 1`) /\ `(array_length t1) = n2 + 1` /\
          ((j:Z)
           (`0 <= j` /\ `j <= n2` ->
            (min_suffix w1 w2 `i3 + 1` j (access t1 j)))))
  (Test8: `i3 >= 0`)
  (Pre24: `0 <= n2` /\ `n2 < (array_length t1)`)
  (old1: Z)
  (Post6: old1 = (access t1 n2))
  (Pre22: `0 <= n2` /\ `n2 < (array_length t1)`)
  (Pre23: `0 <= n2` /\ `n2 < (array_length t1)`)
  (t2: (array Z))
  (Post7: t2 = (store t1 n2 `(access t1 n2) + 1`))
  (j1: Z)
  (Post8: j1 = `n2 - 1`)
  (`(-1) <= j1` /\ `j1 <= n2 - 1`) /\ `(array_length t2) = n2 + 1` /\
  ((k:Z) (`j1 < k` /\ `k <= n2` -> (min_suffix w1 w2 i3 k (access t2 k)))) /\
  ((k:Z)
   (`0 <= k` /\ `k <= j1` -> (min_suffix w1 w2 `i3 + 1` k (access t2 k)))) /\
  (min_suffix w1 w2 `i3 + 1` `j1 + 1` old1).
Proof.
Intuition.
ArraySubst t2.
Rewrite Post7; Clear Post7.
Replace k with n2; [ Idtac | Omega' ].
Unfold min_suffix.
Rewrite (suffix_is_cons n1 w1 i3).
Rewrite suffix_n_is_eps.
AccessSame.
Apply min_dist_eps.
Rewrite <- suffix_n_is_eps with n:=n2 t:=w2.
Apply H13; Omega'.
Omega'.
Rewrite Post7.
AccessOther.
Apply H13; Omega'.
Rewrite Post6.
Replace `n2` with `(j1+1)`; [ Idtac | Omega' ].
Apply H13; Omega'.
Save.

(* Why obligation from file "distance.mlw", characters 1831-2673 *)
Lemma distance_po_12 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post4: ((`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
          ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`))) /\
          `i1 > n2`)
  (i2: Z)
  (Post5: i2 = `n1 - 1`)
  (Variant3: Z)
  (i3: Z)
  (t1: (array Z))
  (Pre26: Variant3 = `i3 + 1`)
  (Pre25: (`(-1) <= i3` /\ `i3 <= n1 - 1`) /\ `(array_length t1) = n2 + 1` /\
          ((j:Z)
           (`0 <= j` /\ `j <= n2` ->
            (min_suffix w1 w2 `i3 + 1` j (access t1 j)))))
  (Test8: `i3 >= 0`)
  (Pre24: `0 <= n2` /\ `n2 < (array_length t1)`)
  (old1: Z)
  (Post6: old1 = (access t1 n2))
  (Pre22: `0 <= n2` /\ `n2 < (array_length t1)`)
  (Pre23: `0 <= n2` /\ `n2 < (array_length t1)`)
  (t2: (array Z))
  (Post7: t2 = (store t1 n2 `(access t1 n2) + 1`))
  (j1: Z)
  (Post8: j1 = `n2 - 1`)
  (j2: Z)
  (old2: Z)
  (t3: (array Z))
  (Post14: ((`(-1) <= j2` /\ `j2 <= n2 - 1`) /\
           `(array_length t3) = n2 + 1` /\
           ((k:Z)
            (`j2 < k` /\ `k <= n2` -> (min_suffix w1 w2 i3 k (access t3 k)))) /\
           ((k:Z)
            (`0 <= k` /\ `k <= j2` ->
             (min_suffix w1 w2 `i3 + 1` k (access t3 k)))) /\
           (min_suffix w1 w2 `i3 + 1` `j2 + 1` old2)) /\ `j2 < 0`)
  (i4: Z)
  (Post15: i4 = `i3 - 1`)
  ((`(-1) <= i4` /\ `i4 <= n1 - 1`) /\ `(array_length t3) = n2 + 1` /\
  ((j:Z)
   (`0 <= j` /\ `j <= n2` -> (min_suffix w1 w2 `i4 + 1` j (access t3 j))))) /\
  (Zwf `0` `i4 + 1` `i3 + 1`).
Proof.
Intuition.
Replace `i4+1` with i3; [ Idtac | Omega' ].
Apply H20; Omega'.
Unfold Zwf; Omega'.
Save.

(* Why obligation from file "distance.mlw", characters 1868-1987 *)
Lemma distance_po_13 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post4: ((`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
          ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`))) /\
          `i1 > n2`)
  (i2: Z)
  (Post5: i2 = `n1 - 1`)
  (`(-1) <= i2` /\ `i2 <= n1 - 1`) /\ `(array_length t0) = n2 + 1` /\
  ((j:Z)
   (`0 <= j` /\ `j <= n2` -> (min_suffix w1 w2 `i2 + 1` j (access t0 j)))).
Proof.
Intuition.
Omega'.
Replace `i2+1` with n1; [ Idtac | Omega' ].
Unfold min_suffix.
Rewrite suffix_n_is_eps.
Replace (access t0 j) with (Zlength (suffix n2 w2 j)).
Exact (min_dist_eps_length (suffix n2 w2 j)).
Rewrite H7.
Apply suffix_length; Omega'.
Omega'.
Save.

(* Why obligation from file "distance.mlw", characters 2681-2685 *)
Lemma distance_po_14 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post4: ((`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
          ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`))) /\
          `i1 > n2`)
  (i2: Z)
  (Post5: i2 = `n1 - 1`)
  (i3: Z)
  (t1: (array Z))
  (Post16: ((`(-1) <= i3` /\ `i3 <= n1 - 1`) /\
           `(array_length t1) = n2 + 1` /\
           ((j:Z)
            (`0 <= j` /\ `j <= n2` ->
             (min_suffix w1 w2 `i3 + 1` j (access t1 j))))) /\
           `i3 < 0`)
  `0 <= 0` /\ `0 < (array_length t1)`.
Proof.
Intuition.
Omega'.
Save.


(* Why obligation from file "distance.mlw", characters 2681-2685 *)
Lemma distance_po_15 : 
  (t: (array Z))
  (w1: (array A))
  (w2: (array A))
  (Pre28: `(array_length w1) = n1` /\ `(array_length w2) = n2` /\
          `(array_length t) = n2 + 1`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post4: ((`0 <= i1` /\ `i1 <= n2 + 1`) /\ `(array_length t0) = n2 + 1` /\
          ((j:Z) (`0 <= j` /\ `j < i1` -> `(access t0 j) = n2 - j`))) /\
          `i1 > n2`)
  (i2: Z)
  (Post5: i2 = `n1 - 1`)
  (i3: Z)
  (t1: (array Z))
  (Post16: ((`(-1) <= i3` /\ `i3 <= n1 - 1`) /\
           `(array_length t1) = n2 + 1` /\
           ((j:Z)
            (`0 <= j` /\ `j <= n2` ->
             (min_suffix w1 w2 `i3 + 1` j (access t1 j))))) /\
           `i3 < 0`)
  (Pre27: `0 <= 0` /\ `0 < (array_length t1)`)
  (min_dist (word_of_array n1 w1) (word_of_array n2 w2) (access t1 `0`)).
Proof.
Intuition.
Cut `i3+1=0`; [ Intro Hi3 | Omega' ].
Rewrite Hi3 in H14.
Unfold word_of_array.
Unfold min_suffix in H14.
Apply (H14 `0`); Omega'.
Save.

