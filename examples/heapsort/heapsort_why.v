(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Omega.
Require heap.
Require Inftree.
Require ZArithRing.

Lemma double_div2 : (x:Z) `(Zdiv2 (2*x)) = x`.
Proof.
Destruct x; Auto.
Save.

Lemma double_div2_bis : (x:Z) `0 <= x` -> `(Zdiv2 (2*x+1)) = x`.
Proof.
Destruct x; Auto.
Intros.
Simpl in H.
Absurd `0 <= (NEG p)`.
Simpl. Compute. Auto. Assumption.
Save.

Lemma lem_div2_0 : (n:Z)`1 <= n` -> `(-1) <= (Zdiv2 (n-2)) <= n-1`.
Proof.
Intros.
Elim (Z_lt_ge_dec `1` n); Intro.
Elim (Z_modulo_2 n).
Intro H0; Elim H0; Clear H0; Intros.
Replace `n-2` with `2*(x-1)`.
Rewrite double_div2.
Omega. Omega.
Intro H0; Elim H0; Clear H0; Intros.
Replace `n-2` with `2*(x-1)+1`.
Rewrite double_div2_bis.
Omega. Omega. Omega. Omega.
Replace n with `1`.
Simpl. Omega. Omega.
Save.

Lemma lem_div2_1 : (n:Z)`1 <= n` -> `0 <= (Zdiv2 (n-2))+1`.
Proof.
Intros n Hn. Generalize (lem_div2_0 n Hn). Omega.
Save.

Lemma lem_div2_2 : (n,i:Z)
  `1 <= n` -> `(Zdiv2 (n-2))+1 <= i <= n-1` -> `2*i >= n-1`.
Proof.
Intros n i Hn.
Elim (Z_lt_ge_dec `1` n); Intro.
Elim (Z_modulo_2 n).
Intro H0; Elim H0; Clear H0; Intros x Hx.
Replace `n-2` with `2*(x-1)`.
Rewrite double_div2.
Omega. Omega. 
Intro H0; Elim H0; Clear H0; Intros x Hx.
Replace `n-2` with `2*(x-1)+1`.
Rewrite double_div2_bis.
Omega. Omega. Omega. Omega.
Replace n with `1`.
Simpl. Omega. Omega.
Save.


(* Obligations. *)

(* Why obligation from file "heapsort.mlw", characters 831-867 *)
Lemma heapsort_po_1 : 
  (t: (array Z))
  (Pre16: `1 <= (array_length t)`)
  (result: Z)
  (Post3: result = (Zdiv2 `(array_length t) - 2`))
  (Variant1: Z)
  (k0: Z)
  (t0: (array Z))
  (Pre6: Variant1 = `k0 + 1`)
  (Pre5: (`(-1) <= k0` /\ `k0 <= (array_length t0) - 1`) /\
         ((i:Z)
          (`k0 + 1 <= i` /\ `i <= (array_length t0) - 1` ->
           (heap t0 `(array_length t0) - 1` i))) /\
         (permut t0 t))
  (Test2: `k0 >= 0`)
  (`0 <= k0` /\ `k0 <= (array_length t0) - 1`) /\
  `(array_length t0) - 1 < (array_length t0)` /\
  ((i:Z)
   (`k0 + 1 <= i` /\ `i <= (array_length t0) - 1` ->
    (heap t0 `(array_length t0) - 1` i))).
Proof.
Intuition.
Save.

(* Why obligation from file "heapsort.mlw", characters 578-890 *)
Lemma heapsort_po_2 : 
  (t: (array Z))
  (Pre16: `1 <= (array_length t)`)
  (result: Z)
  (Post3: result = (Zdiv2 `(array_length t) - 2`))
  (Variant1: Z)
  (k0: Z)
  (t0: (array Z))
  (Pre6: Variant1 = `k0 + 1`)
  (Pre5: (`(-1) <= k0` /\ `k0 <= (array_length t0) - 1`) /\
         ((i:Z)
          (`k0 + 1 <= i` /\ `i <= (array_length t0) - 1` ->
           (heap t0 `(array_length t0) - 1` i))) /\
         (permut t0 t))
  (Test2: `k0 >= 0`)
  (Pre4: (`0 <= k0` /\ `k0 <= (array_length t0) - 1`) /\
         `(array_length t0) - 1 < (array_length t0)` /\
         ((i:Z)
          (`k0 + 1 <= i` /\ `i <= (array_length t0) - 1` ->
           (heap t0 `(array_length t0) - 1` i))))
  (t1: (array Z))
  (Post11: (permut t1 t0) /\
           ((i:Z)
            (`k0 <= i` /\ `i <= (array_length t0) - 1` ->
             (heap t1 `(array_length t0) - 1` i))) /\
           ((i:Z)
            (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
             `(array_length t0) - 1 < i` /\ `i < (array_length t1)` ->
             `(access t1 i) = (access t0 i)`)) /\
           ((v:Z)
            ((inftree t0 `(array_length t0) - 1` v k0) ->
             (inftree t1 `(array_length t0) - 1` v k0))))
  (k1: Z)
  (Post1: k1 = `k0 - 1`)
  ((`(-1) <= k1` /\ `k1 <= (array_length t1) - 1`) /\
  ((i:Z)
   (`k1 + 1 <= i` /\ `i <= (array_length t1) - 1` ->
    (heap t1 `(array_length t1) - 1` i))) /\
  (permut t1 t)) /\ (Zwf `0` `k1 + 1` `k0 + 1`).
Proof.
Intuition (SameLength t1 t0; Try Omega).
Rewrite H10; Auto with *.
Apply permut_trans with t':=t0; Assumption.
Unfold Zwf; Omega'.
Save.

(* Why obligation from file "heapsort.mlw", characters 615-799 *)
Lemma heapsort_po_3 : 
  (t: (array Z))
  (Pre16: `1 <= (array_length t)`)
  (result: Z)
  (Post3: result = (Zdiv2 `(array_length t) - 2`))
  (`(-1) <= result` /\ `result <= (array_length t) - 1`) /\
  ((i:Z)
   (`result + 1 <= i` /\ `i <= (array_length t) - 1` ->
    (heap t `(array_length t) - 1` i))) /\
  (permut t t).
Proof.
Intros.
Generalize (lem_div2_0 (array_length t) Pre16); Intuition Try Omega'.
Apply heap_leaf.
Generalize (lem_div2_1 (array_length t) Pre16); Omega'.
Apply (lem_div2_2 (array_length t) i); Trivial Orelse Omega'.
Auto with datatypes.
Save.

(* Why obligation from file "heapsort.mlw", characters 519-952 *)
Lemma heapsort_po_4 : 
  (t: (array Z))
  (Pre16: `1 <= (array_length t)`)
  (result: Z)
  (Post3: result = (Zdiv2 `(array_length t) - 2`))
  (k0: Z)
  (t0: (array Z))
  (Post2: ((`(-1) <= k0` /\ `k0 <= (array_length t0) - 1`) /\
          ((i:Z)
           (`k0 + 1 <= i` /\ `i <= (array_length t0) - 1` ->
            (heap t0 `(array_length t0) - 1` i))) /\
          (permut t0 t)) /\ `k0 < 0`)
  (heap t0 `(array_length t0) - 1` `0`) /\ (permut t0 t).
Proof.
Intuition.
SameLength t0 t; Auto with *.
Save.

(* Why obligation from file "heapsort.mlw", characters 1484-1497 *)
Lemma heapsort_po_5 : 
  (t: (array Z))
  (Pre16: `1 <= (array_length t)`)
  (t0: (array Z))
  (Post9: (heap t0 `(array_length t0) - 1` `0`) /\ (permut t0 t))
  (result0: Z)
  (Post6: result0 = `(array_length t0) - 1`)
  (Variant3: Z)
  (k0: Z)
  (t1: (array Z))
  (Pre15: Variant3 = k0)
  (Pre14: (`0 <= k0` /\ `k0 <= (array_length t1) - 1`) /\
          ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
          ((`k0 + 1 <= (array_length t1) - 1` ->
            `(access t1 0) <= (access t1 k0 + 1)`)) /\
          ((`k0 + 1 <= (array_length t1) - 1` ->
            (sorted_array t1 `k0 + 1` `(array_length t1) - 1`))) /\
          (permut t1 t))
  (Test4: `k0 >= 1`)
  (`0 <= 0` /\ `0 < (array_length t1)`) /\ `0 <= k0` /\
  `k0 < (array_length t1)`.
Proof.
Intuition.
Save.

(* Why obligation from file "heapsort.mlw", characters 1507-1528 *)
Lemma heapsort_po_6 : 
  (t: (array Z))
  (Pre16: `1 <= (array_length t)`)
  (t0: (array Z))
  (Post9: (heap t0 `(array_length t0) - 1` `0`) /\ (permut t0 t))
  (result0: Z)
  (Post6: result0 = `(array_length t0) - 1`)
  (Variant3: Z)
  (k0: Z)
  (t1: (array Z))
  (Pre15: Variant3 = k0)
  (Pre14: (`0 <= k0` /\ `k0 <= (array_length t1) - 1`) /\
          ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
          ((`k0 + 1 <= (array_length t1) - 1` ->
            `(access t1 0) <= (access t1 k0 + 1)`)) /\
          ((`k0 + 1 <= (array_length t1) - 1` ->
            (sorted_array t1 `k0 + 1` `(array_length t1) - 1`))) /\
          (permut t1 t))
  (Test4: `k0 >= 1`)
  (Pre13: (`0 <= 0` /\ `0 < (array_length t1)`) /\ `0 <= k0` /\
          `k0 < (array_length t1)`)
  (t2: (array Z))
  (Post15: (exchange t2 t1 `0` k0))
  (`0 <= 0` /\ `0 <= k0 - 1`) /\ `k0 - 1 < (array_length t2)` /\
  ((i:Z) (`0 + 1 <= i` /\ `i <= k0 - 1` -> (heap t2 `k0 - 1` i))).
Proof.
Intuition.
SameLength t2 t1; Omega.
Apply heap_id with t:=t1.
Apply heap_weakening. Omega'.
Apply H1; Omega'. Omega'.
Decompose [exchange] Post15; Clear Post15.
Unfold array_id.
Intros i0 Hi0. Symmetry. Apply H18; Omega'.
Save.

(* Why obligation from file "heapsort.mlw", characters 1151-1551 *)
Lemma heapsort_po_7 : 
  (t: (array Z))
  (Pre16: `1 <= (array_length t)`)
  (t0: (array Z))
  (Post9: (heap t0 `(array_length t0) - 1` `0`) /\ (permut t0 t))
  (result0: Z)
  (Post6: result0 = `(array_length t0) - 1`)
  (Variant3: Z)
  (k0: Z)
  (t1: (array Z))
  (Pre15: Variant3 = k0)
  (Pre14: (`0 <= k0` /\ `k0 <= (array_length t1) - 1`) /\
          ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
          ((`k0 + 1 <= (array_length t1) - 1` ->
            `(access t1 0) <= (access t1 k0 + 1)`)) /\
          ((`k0 + 1 <= (array_length t1) - 1` ->
            (sorted_array t1 `k0 + 1` `(array_length t1) - 1`))) /\
          (permut t1 t))
  (Test4: `k0 >= 1`)
  (Pre13: (`0 <= 0` /\ `0 < (array_length t1)`) /\ `0 <= k0` /\
          `k0 < (array_length t1)`)
  (t2: (array Z))
  (Post15: (exchange t2 t1 `0` k0))
  (Pre12: (`0 <= 0` /\ `0 <= k0 - 1`) /\ `k0 - 1 < (array_length t2)` /\
          ((i:Z) (`0 + 1 <= i` /\ `i <= k0 - 1` -> (heap t2 `k0 - 1` i))))
  (t3: (array Z))
  (Post17: (permut t3 t2) /\
           ((i:Z) (`0 <= i` /\ `i <= k0 - 1` -> (heap t3 `k0 - 1` i))) /\
           ((i:Z)
            (`0 <= i` /\ `i < 0` \/ `0 < i` /\ `i < 2 * 0 + 1` \/
             `k0 - 1 < i` /\ `i < (array_length t3)` ->
             `(access t3 i) = (access t2 i)`)) /\
           ((v:Z)
            ((inftree t2 `k0 - 1` v `0`) -> (inftree t3 `k0 - 1` v `0`))))
  (k1: Z)
  (Post4: k1 = `k0 - 1`)
  ((`0 <= k1` /\ `k1 <= (array_length t3) - 1`) /\
  ((i:Z) (`0 <= i` /\ `i <= k1` -> (heap t3 k1 i))) /\
  ((`k1 + 1 <= (array_length t3) - 1` ->
    `(access t3 0) <= (access t3 k1 + 1)`)) /\
  ((`k1 + 1 <= (array_length t3) - 1` ->
    (sorted_array t3 `k1 + 1` `(array_length t3) - 1`))) /\
  (permut t3 t)) /\ (Zwf `0` k1 k0).
Proof.
Intuition.
SameLength t3 t2; Omega.
(* heap *)
Subst k1; Apply H17; Omega'.
(* t[0] <= t[k] *)
Subst k1; Ring `k0-1+1`. 
Rewrite (H16 k0); [ Idtac | Omega' ].
Decompose [exchange] Post15.
Rewrite H24.
Apply inftree_1 with n:=`k0-1`.
Apply H19.
Apply inftree_weakening. Omega'.
Apply inftree_exchange with t1:=t1. Omega'.
Apply inftree_3.
Apply H1; Omega'.
Assumption. Omega'.
(* sorted *)
Subst k1; Ring `k0-1+1`.  
Elim (Z_le_lt_eq_dec k0 `(array_length t1)-1` H6); Intro.
  (* k0 < N-1 *)
  Replace k0 with `(k0+1)-1`; [ Idtac | Omega' ].
  Apply left_extension. Omega'. Omega'.
  Apply sorted_array_id with t1:=t2. 
  Apply sorted_array_id with t1:=t1. 
  SameLength t3 t2; SameLength t2 t1; SameLength t1 t.
  Rewrite H20; Rewrite H21. Apply H7; Omega'.
  Decompose [exchange] Post15.
  Unfold array_id. Intros i Hi. Symmetry. 
  SameLength t3 t2; Apply H25; Try Omega'.
  Unfold array_id. Intros i Hi. Symmetry. Apply H16; Omega'.
  (* t3[k0] <= t3[k0+1] *)
  Ring `k0+1-1`. 
  Rewrite (H16 k0); [ Idtac | Omega' ].
  Rewrite (H16 `k0+1`); 
    [ Idtac | SameLength t3 t2; SameLength t2 t1; Omega' ].
  Decompose [exchange] Post15.
  Rewrite H24. Rewrite (H25 `k0+1`); [ Idtac | Omega' | Omega' | Omega' ].
  Apply H4; Omega'.
  (* k0 = N-1 *)
  Rewrite b. 
  Unfold sorted_array.
  Intros HN x HHx Hx. 
  Absurd `x >= (array_length t3)-1`; 
  SameLength t3 t2; SameLength t2 t1; Omega'.
(* (permut t3 t) *)
Apply permut_trans with t':=t2; Try Assumption. 
Apply permut_trans with t':=t1.
Apply exchange_is_permut with i:=`0` j:=k0. Assumption. 
Assumption. 
(* Zwf *)
Unfold Zwf; Omega'.
Save.

(* Why obligation from file "heapsort.mlw", characters 1188-1452 *)
Lemma heapsort_po_8 : 
  (t: (array Z))
  (Pre16: `1 <= (array_length t)`)
  (t0: (array Z))
  (Post9: (heap t0 `(array_length t0) - 1` `0`) /\ (permut t0 t))
  (result0: Z)
  (Post6: result0 = `(array_length t0) - 1`)
  (`0 <= result0` /\ `result0 <= (array_length t0) - 1`) /\
  ((i:Z) (`0 <= i` /\ `i <= result0` -> (heap t0 result0 i))) /\
  ((`result0 + 1 <= (array_length t0) - 1` ->
    `(access t0 0) <= (access t0 result0 + 1)`)) /\
  ((`result0 + 1 <= (array_length t0) - 1` ->
    (sorted_array t0 `result0 + 1` `(array_length t0) - 1`))) /\
  (permut t0 t).
Proof.
Intuition SameLength t0 t; Try Omega.
Apply heap_all.
Subst result0; Assumption.
Tauto.
Intro; Absurd `(array_length t0)-1+1 <= (array_length t0)-1`; Omega'.
Save.

(* Why obligation from file "heapsort.mlw", characters 1109-1551 *)
Lemma heapsort_po_9 : 
  (t: (array Z))
  (Pre16: `1 <= (array_length t)`)
  (t0: (array Z))
  (Post9: (heap t0 `(array_length t0) - 1` `0`) /\ (permut t0 t))
  (result0: Z)
  (Post6: result0 = `(array_length t0) - 1`)
  (k0: Z)
  (t1: (array Z))
  (Post5: ((`0 <= k0` /\ `k0 <= (array_length t1) - 1`) /\
          ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
          ((`k0 + 1 <= (array_length t1) - 1` ->
            `(access t1 0) <= (access t1 k0 + 1)`)) /\
          ((`k0 + 1 <= (array_length t1) - 1` ->
            (sorted_array t1 `k0 + 1` `(array_length t1) - 1`))) /\
          (permut t1 t)) /\ `k0 < 1`)
  (sorted_array t1 `0` `(array_length t1) - 1`) /\ (permut t1 t).
Proof.
Intuition.
Elim (Z_le_lt_eq_dec `1` (array_length t) Pre16); Intro.
  (* 1 < N *)
  Replace `0` with `1-1`; [ Idtac | Omega' ].
  Apply left_extension. Omega'. Omega'.
  Replace `1` with `k0+1`; [ Idtac | Omega' ].
  Replace `(array_length t1)-(k0+1)` with `(array_length t1)-1`; 
  [ Idtac | Omega' ].
  Apply H6; SameLength t1 t; Omega'.
  Replace `1-1` with `0`; [ Idtac | Omega' ]. (* Ring `1-1`. *)
  Replace `1` with `k0+1`; [ Idtac | Omega' ].
  Apply H4; SameLength t1 t; Omega'.
  (* 1 = N *)
  Unfold sorted_array. 
  Intros HN x HHx Hx. 
  Absurd `x >= (array_length t)-1`; SameLength t1 t; Omega'.
Save.

Require swap_why.
Require downheap_why.


