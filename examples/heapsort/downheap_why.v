(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Omega.
Require Heap.
Require Inftree.

Lemma R11 : (k:Z) `2*k+1+1` = `2*k+2`.
Proof.
Intro; Omega.
Save.

(* To annotate the recursive function downheap, it is convenient to
 * introduce the following predicate, which expresses that j is the
 * greatest son of k. *)

Implicit Arguments On.

Inductive select_son [N:Z; t:(array N Z); k,n,j:Z] : Prop :=
    select_left_son : 
      `j = 2*k+1` -> (`2*k+2 <= n` -> (Zge #t[j] #t[`2*k+2`])) 
        -> (select_son t k n j)
  | select_right_son :
      `j = 2*k+2` -> `j <= n` -> (Zge #t[j] #t[`2*k+1`]) 
        -> (select_son t k n j).

Implicit Arguments Off.

(* The correctness of downheap requires the two following lemmas *)

Lemma Lemma_1 : (N:Z)(t0,t1,t2:(array N Z))
    (n0,k0,j':Z)
    `2*k0+1 <= n0`
 -> (select_son t0 k0 n0 j')
 -> `(access   t0 k0) < (access   t0 j')`
 -> (exchange t1 t0 k0 j')
 -> `0 <= k0 <= n0`
 -> `n0 < N`
 -> ((i:Z)`k0+1 <= i <= n0`->(heap t0 n0 i))
 -> ((i:Z)`j' <= i <= n0`->(heap t2 n0 i))
 -> ((i:Z)
        `0 <= i < j'`\/`j' < i < 2*j'+1`\/`n0 < i < N`
        ->`(access   t2 i) = (access   t1 i)`)
 -> ((v:Z)(inftree t1 n0 v j')->(inftree t2 n0 v j'))
 -> (i:Z)`k0 < i < j'`->(heap t2 n0 i).
Proof.
Intros. Apply heap_cons.
Elim H0; Omega'.
(* branch 2i+1 *)
Intro. Rewrite (H7 i). Rewrite (H7 `2*i+1`).
Decompose [exchange] H2. Rewrite (H15 i). Rewrite (H15 `2*i+1`).
Generalize H10. Elim (H5 i); Intros. Exact (H17 H23).
Omega'. Omega'. Omega'.
Elim H0; Omega'. Omega'. Omega'. Omega'.
Elim H0; Omega'. Elim H0; Omega'. 
Intro. Apply H6; Elim H0; Omega'.
(* branch 2i+2 *)
Intro. Rewrite (H7 i). Rewrite (H7 `2*i+2`).
Decompose [exchange] H2. Rewrite (H15 i). Rewrite (H15 `2*i+2`).
Generalize H10. Elim (H5 i); Intros. Exact (H20 H23).
Omega'. Omega'. Omega'. 
Elim H0; Omega'. Omega'. Omega'. Omega'.
Elim H0; Omega'. Elim H0; Omega'. 
Intro. Apply H6; Elim H0; Omega'.
Save.

Lemma Lemma_2 : (N:Z)(t0,t1,t2:(array N Z))
    (n0,k0,j':Z)
    `2*k0+1 <= n0`
 -> (select_son t0 k0 n0 j')
 -> `(access   t0 k0) < (access   t0 j')`
 -> (exchange t1 t0 k0 j')
 -> `0 <= k0 <= n0`
 -> `n0 < N`
 -> ((i:Z)`k0+1 <= i <= n0`->(heap t0 n0 i))
 -> ((i:Z)`j' <= i <= n0`->(heap t2 n0 i))
 -> ((i:Z)
        `0 <= i < j'`\/`j' < i < 2*j'+1`\/`n0 < i < N`
        ->`(access   t2 i) = (access   t1 i)`)
 -> ((v:Z)(inftree t1 n0 v j')->(inftree t2 n0 v j'))
 -> (i:Z)`k0 <= i <= n0`->(heap t2 n0 i).
Proof.
Intros.
Elim (Z_lt_ge_dec i j'); Intro HHi.
Elim (Z_le_lt_eq_dec k0 i); [ Intro HHHi | Intro HHHi | Intuition ].

(* 1. k0 < i < j' *)
Apply (Lemma_1 N t0 t1 t2 n0 k0 j'); Assumption Orelse Omega'.

(* 2. k0 = i *)
Apply heap_cons.
Omega'.
(* branch 2i+1 *)
(* t[k] >= t[2k+1] *)
Intro. Elim H0; Intros.
  (* j' = 2k+1 *)
  Rewrite <- HHHi. Rewrite <- H11.
  Rewrite (H7 k0). Decompose [exchange] H2. Rewrite H15.
  Apply Zle_ge. Apply inftree_1 with n:=n0.
  Apply H8.
  Apply inftree_2 with t1:=t0 k:=k0. Omega'. 
  Apply inftree_3.
  Apply H5; Omega'. Assumption. Omega'. Omega'. Omega'.
  (* j' = 2k+2 *)
  Rewrite <- HHHi.
  Rewrite (H7 k0). Decompose [exchange] H2. Rewrite H16.
  Rewrite (H7 `2*k0+1`). Rewrite (H18 `2*k0+1`).
  Omega'. Omega'. Omega'. Omega'. Omega'. Omega'. 
(* (heap t2 n (2k+1)) *)
Intro. Elim H0; Intros.
  (* j' = 2k+1 *)
  Apply H6; Omega'.
  (* j' = 2k+2 *)
  Apply (Lemma_1 N t0 t1 t2 n0 k0 j'); Assumption Orelse Omega'.
(* branch 2i+2 *)
(* t[k] >= t[2k+2] *)
Intro. Elim H0; Intros.
  (* j' = 2k+1 *)
  Rewrite <- HHHi.
  Rewrite (H7 k0). Decompose [exchange] H2. Rewrite H15.
  Rewrite (H7 `2*k0+2`). Rewrite (H17 `2*k0+2`).
  Omega'. Omega'. Omega'. Omega'. Omega'. Omega'. 
  (* j' = 2k+2 *)
  Rewrite <- HHHi. Rewrite <- H11.
  Rewrite (H7 k0). Decompose [exchange] H2. Rewrite H16.
  Apply Zle_ge. Apply inftree_1 with n:=n0.
  Apply H8.
  Apply inftree_2 with t1:=t0 k:=k0. Omega'. 
  Apply inftree_3.
  Apply H5; Omega'. Assumption. Omega'. Omega'. Omega'.
(* (heap t2 n (2k+2)) *)
Intro. Elim H0; Intros.
  (* j' = 2k+1 *)
  Apply H6; Omega'.
  (* j' = 2k+2 *)
  Apply H6; Omega'.

(* 3. i >= j' *)
Apply H6; Omega'.
Save.


(* Obligations *)

Lemma downheap_po_1 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma downheap_po_2 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test8: `result <= n`)
  (Test5: `result + 1 <= n`)
  `0 <= result + 1` /\ `result + 1 < N`.
Proof.
Intros; Omega'.
Save.

Lemma downheap_po_3 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test8: `result <= n`)
  (Test5: `result + 1 <= n`)
  (Pre2: `0 <= result + 1` /\ `result + 1 < N`)
  `0 <= result` /\ `result < N`.
Proof.
Intros; Omega'.
Save.

Lemma downheap_po_4 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test8: `result <= n`)
  (Test5: `result + 1 <= n`)
  (Test4: `(access t0 result) < (access t0 result + 1)`)
  (select_son t0 k n `result + 1`).
Proof.
Intros.
Rewrite Post1; Rewrite (R11 k0).
Rewrite Post1 in Test4.
Apply select_right_son; 
  [ Reflexivity | Omega' | Rewrite (R11 k0) in Test4; Omega' ].
Save.

Lemma downheap_po_5 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test8: `result <= n`)
  (Test5: `result + 1 <= n`)
  (Test3: `(access t0 result) >= (access t0 result + 1)`)
  (select_son t0 k n result).
Proof.
Intros.
Rewrite Post1; Rewrite Post1 in Test3.
Apply select_left_son; 
  [ Reflexivity | Rewrite (R11 k0) in Test3; Intro; Assumption ].
Save.

Lemma downheap_po_6 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test8: `result <= n`)
  (Test2: `result + 1 > n`)
  (select_son t0 k n result).
Proof.
Intros.
Rewrite Post1.
Apply select_left_son; [ Reflexivity | Intro; Absurd `2*k0+2 <= n0`; Omega' ].
Save.

Lemma downheap_po_7 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test8: `result <= n`)
  (result1: Z)
  (Post10: (select_son t0 k n result1))
  `0 <= result1` /\ `result1 < N`.
Proof.
Intros; Elim Post10; Intros; Omega'.
Save.

Lemma downheap_po_8 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test8: `result <= n`)
  (result1: Z)
  (Post10: (select_son t0 k n result1))
  (Pre4: `0 <= result1` /\ `result1 < N`)
  `0 <= k` /\ `k < N`.
Proof.
Intros; Omega'.
Save.

Lemma downheap_po_9 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test8: `result <= n`)
  (result1: Z)
  (Post10: (select_son t0 k n result1))
  (Test7: `(access t0 k) < (access t0 result1)`)
  `0 <= k` /\ `k < N` /\ (`0 <= result1` /\ `result1 < N`).
Proof.
Intros; Elim Post10; Intros; Omega'.
Save.

Lemma downheap_po_10 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test8: `result <= n`)
  (result1: Z)
  (Post10: (select_son t0 k n result1))
  (Test7: `(access t0 k) < (access t0 result1)`)
  (t1: (array N Z))
  (Post21: (exchange t1 t0 k result1))
  `0 <= result1` /\ `result1 <= n` /\ `n < N` /\
  ((i:Z) (`result1 + 1 <= i` /\ `i <= n` -> (heap t1 n i))).
Proof.
Intuition; Try (Elim Post10; Omega').
Apply heap_id with t := t0.
Apply H7; Elim Post10; Omega'.
Unfold array_id. Intros i' Hi'.
Elim Post21; Intros.
Symmetry; Apply (H13 i'); Elim Post10; Omega'.
Save.

Lemma downheap_po_11 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test8: `result <= n`)
  (result1: Z)
  (Post10: (select_son t0 k n result1))
  (Test7: `(access t0 k) < (access t0 result1)`)
  (t1: (array N Z))
  (Post21: (exchange t1 t0 k result1))
  (Pre7: `0 <= result1` /\ `result1 <= n` /\ `n < N` /\
         ((i:Z) (`result1 + 1 <= i` /\ `i <= n` -> (heap t1 n i))))
  (Zwf `0` `n - result1` Variant1).
Proof.
Intros; Unfold Zwf; Decompose [select_son] Post10; Omega'.
Save.

Lemma downheap_po_12 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test8: `result <= n`)
  (result1: Z)
  (Post10: (select_son t0 k n result1))
  (Test7: `(access t0 k) < (access t0 result1)`)
  (t1: (array N Z))
  (Post21: (exchange t1 t0 k result1))
  (t2: (array N Z))
  (Post23: (permut t2 t1) /\
           ((i:Z) (`result1 <= i` /\ `i <= n` -> (heap t2 n i))) /\
           ((i:Z)
            (`0 <= i` /\ `i < result1` \/ `result1 < i` /\
             `i < 2 * result1 + 1` \/ `n < i` /\ `i < N` ->
             (access t2 i) = (access t1 i))) /\
           ((v:Z) ((inftree t1 n v result1) -> (inftree t2 n v result1))))
  (permut t2 t0) /\ ((i:Z) (`k <= i` /\ `i <= n` -> (heap t2 n i))) /\
  ((i:Z)
   (`0 <= i` /\ `i < k` \/ `k < i` /\ `i < 2 * k + 1` \/ `n < i` /\
    `i < N` -> (access t2 i) = (access t0 i))) /\
  ((v:Z) ((inftree t0 n v k) -> (inftree t2 n v k))).
Proof.
Intuition.
(* permut *)
Apply permut_trans with t' := t1.
Intuition. Apply exchange_is_permut with i:=k0 j:=result1; Assumption.
(* heap *)
Apply (Lemma_2 N0 t0 t1 t2 n0 k0 result1); Assumption Orelse Omega'.
(* unchanged parts of the array *)
Rewrite (H8 i); 
[ Decompose [exchange] Post21; Apply H17 | Idtac ];
Decompose [select_son] Post10; Omega'.
Rewrite (H8 i); 
[ Decompose [exchange] Post21; Apply H17 | Idtac ];
Decompose [select_son] Post10; Omega'.
Rewrite (H8 i); 
[ Decompose [exchange] Post21; Apply H17 | Idtac ];
Decompose [select_son] Post10; Omega'.
(* inftree *)
Apply inftree_cons.
Split; Assumption.
Rewrite (H8 k0). 
Decompose [exchange] Post21. Rewrite H14. 
Elim Post10; Intros.
  (* j' = 2k+1 *)
  Rewrite H17. Generalize Test8; Rewrite Post1. Case H10; Intros.
  Apply inftree_1 with n:=n0. Auto.
  (* j' = 2k+2 *)
  Generalize H18. Rewrite H17. Case H10; Intros.
  Apply inftree_1 with n:=n0. Auto.
Elim Post10; Intros; Omega'.
  (* branch 2k+1 *)
  Intro. Elim Post10; Intros.
    (* j' = 2k+1 *)
    Rewrite <- H13. Apply H11. 
    Apply inftree_2 with t1:=t0 k:=k0. Omega'. 
    Rewrite H13. Generalize H12. Case H10; Auto.
    Assumption. Omega'. Omega'.
    (* j' = 2k+2 *)
    Apply inftree_trans with v:=#t2[`2*k0+1`].
    Rewrite (H8 `2*k0+1`).
    Decompose [exchange] Post21. Rewrite (H20 `2*k0+1`).
    Generalize H12. Case H10; Intros.
    Apply inftree_1 with n:=n0. Auto.
    Omega'. Omega'. Omega'. Omega'.
    Apply inftree_3.
    Apply (Lemma_2 N0 t0 t1 t2 n0 k0 result1); Assumption Orelse Omega'.
  (* branch 2k+2 *)
  Intro. Elim Post10; Intros.
    (* j' = 2k+1 *)
    Apply inftree_trans with v:=#t2[`2*k0+2`].
    Rewrite (H8 `2*k0+2`).
    Decompose [exchange] Post21. Rewrite (H19 `2*k0+2`).
    Generalize H12. Case H10; Intros.
    Apply inftree_1 with n:=n0. Auto.
    Omega'. Omega'. Omega'. Omega'.
    Apply inftree_3.
    Apply H9; Omega'.
    (* j' = 2k+2 *)
    Rewrite <- H13. Apply H11. 
    Apply inftree_2 with t1:=t0 k:=k0. Omega'. 
    Rewrite H13. Generalize H12. Case H10; Auto.
    Assumption. Omega'. Omega'.
Save.

Lemma downheap_po_13 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test8: `result <= n`)
  (result1: Z)
  (Post10: (select_son t0 k n result1))
  (Test6: `(access t0 k) >= (access t0 result1)`)
  (permut t0 t0) /\ ((i:Z) (`k <= i` /\ `i <= n` -> (heap t0 n i))) /\
  ((i:Z)
   (`0 <= i` /\ `i < k` \/ `k < i` /\ `i < 2 * k + 1` \/ `n < i` /\
    `i < N` -> (access t0 i) = (access t0 i))) /\
  ((v:Z) ((inftree t0 n v k) -> (inftree t0 n v k))).
Proof.
Intuition.
Elim (Z_le_lt_eq_dec k0 i); [ Intro HHHi | Intro HHHi | Intuition ].
(* k0 < i *)
Apply H7; Omega'.
(* k0 = i *)
Rewrite <- HHHi. Apply heap_cons.
Omega'.
Intro. Elim Post10; Intros.
Rewrite <- H10. Assumption. Omega'.
Intro. Apply H7; Omega'.
Intro. Elim Post10; Intros.
Omega'. Rewrite <- H10. Assumption.
Intro. Apply H7; Omega'.
Save.

Lemma downheap_po_14 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= k` /\ `k <= n` /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N: Z)
  (k: Z)
  (n: Z)
  (t0: (array N Z))
  (Pre9: `0 <= k` /\ `k <= n` /\ `n < N` /\
         ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t0 n i))))
  (Pre8: Variant1 = `n - k`)
  (result: Z)
  (Post1: result = `2 * k + 1`)
  (Test1: `result > n`)
  (permut t0 t0) /\ ((i:Z) (`k <= i` /\ `i <= n` -> (heap t0 n i))) /\
  ((i:Z)
   (`0 <= i` /\ `i < k` \/ `k < i` /\ `i < 2 * k + 1` \/ `n < i` /\
    `i < N` -> (access t0 i) = (access t0 i))) /\
  ((v:Z) ((inftree t0 n v k) -> (inftree t0 n v k))).
Proof.
Intuition.
Elim (Z_le_lt_eq_dec k0 i); [ Intro HHHi | Intro HHHi | Intuition ].
Apply H7; Omega'.
Rewrite <- HHHi. Apply heap_cons.
Omega'.
Intro; Absurd `2*k0+1 > n0`; Omega'.
Intro; Absurd `2*k0+1 > n0`; Omega'.
Intro; Absurd `2*k0+2 > n0`; Omega'.
Intro; Absurd `2*k0+2 > n0`; Omega'.
Save.
