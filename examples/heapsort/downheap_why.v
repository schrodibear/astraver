(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Omega.
Require heap.
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
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (well_founded (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma downheap_po_2 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (Test5: `j + 1 <= n0`)
  `0 <= j + 1` /\ `j + 1 < N0`.
Proof.
Intros; Omega'.
Save.

Lemma downheap_po_3 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (Test5: `j + 1 <= n0`)
  (Pre2: `0 <= j + 1` /\ `j + 1 < N0`)
  `0 <= j` /\ `j < N0`.
Proof.
Intros; Omega'.
Save.

Lemma downheap_po_4 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (Test5: `j + 1 <= n0`)
  (Test4: `(access t0 j) < (access t0 j + 1)`)
  (select_son t0 k0 n0 `j + 1`).
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
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (Test5: `j + 1 <= n0`)
  (Test3: `(access t0 j) >= (access t0 j + 1)`)
  (select_son t0 k0 n0 j).
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
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (Test2: `j + 1 > n0`)
  (select_son t0 k0 n0 j).
Proof.
Intros.
Rewrite Post1.
Apply select_left_son; [ Reflexivity | Intro; Absurd `2*k+2 <= n`; Omega' ].
Save.

Lemma downheap_po_7 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post10: (select_son t0 k0 n0 j'))
  `0 <= j'` /\ `j' < N0`.
Proof.
Intros; Elim Post10; Intros; Omega'.
Save.

Lemma downheap_po_8 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post10: (select_son t0 k0 n0 j'))
  (Pre4: `0 <= j'` /\ `j' < N0`)
  `0 <= k0` /\ `k0 < N0`.
Proof.
Intros; Omega'.
Save.

Lemma downheap_po_9 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post10: (select_son t0 k0 n0 j'))
  (Test7: `(access t0 k0) < (access t0 j')`)
  (`0 <= k0` /\ `k0 < N0`) /\ `0 <= j'` /\ `j' < N0`.
Proof.
Intros; Elim Post10; Intros; Omega'.
Save.

Lemma downheap_po_10 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post10: (select_son t0 k0 n0 j'))
  (Test7: `(access t0 k0) < (access t0 j')`)
  (t1: (array N0 Z))
  (Post21: (exchange t1 t0 k0 j'))
  (`0 <= j'` /\ `j' <= n0`) /\ `n0 < N0` /\
  ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))).
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
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post10: (select_son t0 k0 n0 j'))
  (Test7: `(access t0 k0) < (access t0 j')`)
  (t1: (array N0 Z))
  (Post21: (exchange t1 t0 k0 j'))
  (Pre8: (`0 <= j'` /\ `j' <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))))
  (Zwf `0` `n0 - j'` Variant1).
Proof.
Intros; Unfold Zwf; Decompose [select_son] Post10; Omega'.
Save.

Lemma downheap_po_12 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post10: (select_son t0 k0 n0 j'))
  (Test7: `(access t0 k0) < (access t0 j')`)
  (t1: (array N0 Z))
  (Post21: (exchange t1 t0 k0 j'))
  (Pre8: (`0 <= j'` /\ `j' <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))))
  (`0 <= j'` /\ `j' <= n0`) /\ `n0 < N0` /\
  ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))).
Proof.
Intuition.
Save.

Lemma downheap_po_13 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post10: (select_son t0 k0 n0 j'))
  (Test7: `(access t0 k0) < (access t0 j')`)
  (t1: (array N0 Z))
  (Post21: (exchange t1 t0 k0 j'))
  (t2: (array N0 Z))
  (Post23: (permut t2 t1) /\
           ((i:Z) (`j' <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
           ((i:Z)
            (`0 <= i` /\ `i < j'` \/ `j' < i` /\ `i < 2 * j' + 1` \/
             `n0 < i` /\ `i < N0` -> `(access t2 i) = (access t1 i)`)) /\
           ((v:Z) ((inftree t1 n0 v j') -> (inftree t2 n0 v j'))))
  (permut t2 t0) /\ ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
  ((i:Z)
   (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/ `n0 < i` /\
    `i < N0` -> `(access t2 i) = (access t0 i)`)) /\
  ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))).
Proof.
Intuition.

(* permut *)
Apply permut_trans with t' := t1.
Intuition. Apply exchange_is_permut with i:=k0 j:=j'; Assumption.
(* heap *)
Apply (Lemma_2 N0 t0 t1 t2 n0 k0 j'); Assumption Orelse Omega'.
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
    Apply (Lemma_2 N0 t0 t1 t2 n0 k0 j'); Assumption Orelse Omega'.
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

Lemma downheap_po_14 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post10: (select_son t0 k0 n0 j'))
  (Test6: `(access t0 k0) >= (access t0 j')`)
  (permut t0 t0) /\ ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t0 n0 i))) /\
  ((i:Z)
   (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/ `n0 < i` /\
    `i < N0` -> `(access t0 i) = (access t0 i)`)) /\
  ((v:Z) ((inftree t0 n0 v k0) -> (inftree t0 n0 v k0))).
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

Lemma downheap_po_15 : 
  (N: Z)
  (k: Z)
  (n: Z)
  (t: (array N Z))
  (Pre11: (`0 <= k` /\ `k <= n`) /\ `n < N` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (N0: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array N0 Z))
  (Pre10: Variant1 = `n0 - k0`)
  (Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post1: j = `2 * k0 + 1`)
  (Test1: `j > n0`)
  (permut t0 t0) /\ ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t0 n0 i))) /\
  ((i:Z)
   (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/ `n0 < i` /\
    `i < N0` -> `(access t0 i) = (access t0 i)`)) /\
  ((v:Z) ((inftree t0 n0 v k0) -> (inftree t0 n0 v k0))).
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

Require swap_why.

Definition downheap := (* validation *)
  [N: Z; k: Z; n: Z; t: (array N Z); Pre11: (`0 <= k` /\ `k <= n`) /\
   `n < N` /\ ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i)))]
    (well_founded_induction Z (Zwf ZERO) (downheap_po_1 N k n t Pre11)
      [Variant1: Z](N0: Z)(k0: Z)(n0: Z)(t0: (array N0 Z))
      (_: Variant1 = `n0 - k0`)(_0: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
      ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
      (sig_2 (array N0 Z) unit [t1: (array N0 Z)][result: unit]
       ((permut t1 t0) /\
       ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t1 n0 i))) /\
       ((i:Z)
        (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/ `n0 < i` /\
         `i < N0` -> `(access t1 i) = (access t0 i)`)) /\
       ((v:Z) ((inftree t0 n0 v k0) -> (inftree t1 n0 v k0)))))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (N0: Z)(k0: Z)(n0: Z)(t0: (array N0 Z))(_: Variant2 = `n0 - k0`)
       (_0: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
       ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
       (sig_2 (array N0 Z) unit [t1: (array N0 Z)][result: unit]
        ((permut t1 t0) /\
        ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t1 n0 i))) /\
        ((i:Z)
         (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/ `n0 < i` /\
          `i < N0` -> `(access t1 i) = (access t0 i)`)) /\
        ((v:Z) ((inftree t0 n0 v k0) -> (inftree t1 n0 v k0)))));
       N0: Z; k0: Z; n0: Z; t0: (array N0 Z); Pre10: Variant1 = `n0 - k0`;
       Pre9: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < N0` /\
       ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i)))]
        let (j, Post1) = (exist_1 [result: Z]
          result = `2 * k0 + 1` `2 * k0 + 1` (refl_equal ? `2 * k0 + 1`)) in
        let (t1, result, Post6) =
          let (result, Bool4) =
            let (result1, Post7) = (Z_le_gt_bool j n0) in
            (exist_1 [result2: bool]
            (if result2 then `j <= n0` else `j > n0`) result1 Post7) in
          (Cases (btest [result:bool](if result then `j <= n0` else `j > n0`)
                  result Bool4) of
          | (left Test8) =>
              let (t1, result0, Post9) =
                let (j', Post10) =
                  let (result0, Bool3) =
                    let (result2, Post11) = (Z_le_gt_bool `j + 1` n0) in
                    (exist_1 [result3: bool]
                    (if result3 then `j + 1 <= n0` else `j + 1 > n0`) 
                    result2 Post11) in
                  (Cases (btest
                          [result0:bool](if result0 then `j + 1 <= n0`
                                         else `j + 1 > n0`)
                          result0 Bool3) of
                  | (left Test5) =>
                      let (result1, Post13) =
                        let (result1, Bool2) =
                          let Pre2 =
                            (downheap_po_2 N k n t Pre11 Variant1 N0 k0 n0 t0
                            Pre10 Pre9 j Post1 Test8 Test5) in
                          let result2 =
                            let Pre3 =
                              (downheap_po_3 N k n t Pre11 Variant1 N0 k0 n0
                              t0 Pre10 Pre9 j Post1 Test8 Test5 Pre2) in
                            (Z_lt_ge_bool (access t0 j)) in
                          let (result3, Post14) =
                            (result2 (access t0 `j + 1`)) in
                          (exist_1 [result4: bool]
                          (if result4
                           then `(access t0 j) < (access t0 j + 1)`
                           else `(access t0 j) >= (access t0 j + 1)`) 
                          result3 Post14) in
                        (Cases (btest
                                [result1:bool](if result1
                                               then `(access t0 j) <
                                                     (access t0 j + 1)`
                                               else `(access t0 j) >=
                                                     (access t0 j + 1)`)
                                result1 Bool2) of
                        | (left Test4) =>
                            let (result2, Post16) = (exist_1 [result2: Z]
                              (select_son t0 k0 n0 result2) `j + 1`
                              (downheap_po_4 N k n t Pre11 Variant1 N0 k0 n0
                              t0 Pre10 Pre9 j Post1 Test8 Test5 Test4)) in
                            (exist_1 [result3: Z]
                            (select_son t0 k0 n0 result3) result2 Post16)
                        | (right Test3) =>
                            let (result2, Post15) = (exist_1 [result2: Z]
                              (select_son t0 k0 n0 result2) j
                              (downheap_po_5 N k n t Pre11 Variant1 N0 k0 n0
                              t0 Pre10 Pre9 j Post1 Test8 Test5 Test3)) in
                            (exist_1 [result3: Z]
                            (select_son t0 k0 n0 result3) result2 Post15) end) in
                      (exist_1 [result2: Z]
                      (select_son t0 k0 n0 result2) result1 Post13)
                  | (right Test2) =>
                      let (result1, Post12) = (exist_1 [result1: Z]
                        (select_son t0 k0 n0 result1) j
                        (downheap_po_6 N k n t Pre11 Variant1 N0 k0 n0 t0
                        Pre10 Pre9 j Post1 Test8 Test2)) in
                      (exist_1 [result2: Z]
                      (select_son t0 k0 n0 result2) result1 Post12) end) in
                let (t1, result0, Post17) =
                  let (result0, Bool1) =
                    let Pre4 =
                      (downheap_po_7 N k n t Pre11 Variant1 N0 k0 n0 t0 Pre10
                      Pre9 j Post1 Test8 j' Post10) in
                    let result1 =
                      let Pre5 =
                        (downheap_po_8 N k n t Pre11 Variant1 N0 k0 n0 t0
                        Pre10 Pre9 j Post1 Test8 j' Post10 Pre4) in
                      (Z_lt_ge_bool (access t0 k0)) in
                    let (result2, Post18) = (result1 (access t0 j')) in
                    (exist_1 [result3: bool]
                    (if result3 then `(access t0 k0) < (access t0 j')`
                     else `(access t0 k0) >= (access t0 j')`) result2
                    Post18) in
                  (Cases (btest
                          [result0:bool](if result0
                                         then `(access t0 k0) <
                                               (access t0 j')`
                                         else `(access t0 k0) >=
                                               (access t0 j')`)
                          result0 Bool1) of
                  | (left Test7) =>
                      let (t1, result1, Post20) =
                        let (t1, result1, Post21) =
                          let Pre6 =
                            (downheap_po_9 N k n t Pre11 Variant1 N0 k0 n0 t0
                            Pre10 Pre9 j Post1 Test8 j' Post10 Test7) in
                          let (t1, result3, Post22) =
                            (swap N0 k0 j' t0 Pre6) in
                          (exist_2 [t2: (array N0 Z)][result4: unit]
                          (exchange t2 t0 k0 j') t1 result3 Post22) in
                        let (t2, result2, Post23) =
                          let Pre8 =
                            (downheap_po_10 N k n t Pre11 Variant1 N0 k0 n0
                            t0 Pre10 Pre9 j Post1 Test8 j' Post10 Test7 t1
                            Post21) in
                          let (t2, result4, Post24) =
                            ((wf1 `n0 - j'`)
                              (downheap_po_11 N k n t Pre11 Variant1 N0 k0 n0
                              t0 Pre10 Pre9 j Post1 Test8 j' Post10 Test7 t1
                              Post21 Pre8) N0 j' n0 t1
                              (refl_equal ? `n0 - j'`)
                              (downheap_po_12 N k n t Pre11 Variant1 N0 k0 n0
                              t0 Pre10 Pre9 j Post1 Test8 j' Post10 Test7 t1
                              Post21 Pre8)) in
                          (exist_2 [t3: (array N0 Z)][result5: unit]
                          (permut t3 t1) /\
                          ((i:Z) (`j' <= i` /\ `i <= n0` -> (heap t3 n0 i))) /\
                          ((i:Z)
                           (`0 <= i` /\ `i < j'` \/ `j' < i` /\
                            `i < 2 * j' + 1` \/ `n0 < i` /\ `i < N0` ->
                            `(access t3 i) = (access t1 i)`)) /\
                          ((v:Z)
                           ((inftree t1 n0 v j') -> (inftree t3 n0 v j'))) 
                          t2 result4 Post24) in
                        (exist_2 [t3: (array N0 Z)][result3: unit]
                        (permut t3 t0) /\
                        ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t3 n0 i))) /\
                        ((i:Z)
                         (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                          `i < 2 * k0 + 1` \/ `n0 < i` /\ `i < N0` ->
                          `(access t3 i) = (access t0 i)`)) /\
                        ((v:Z) ((inftree t0 n0 v k0) -> (inftree t3 n0 v k0))) 
                        t2 result2
                        (downheap_po_13 N k n t Pre11 Variant1 N0 k0 n0 t0
                        Pre10 Pre9 j Post1 Test8 j' Post10 Test7 t1 Post21 t2
                        Post23)) in
                      (exist_2 [t2: (array N0 Z)][result2: unit]
                      (permut t2 t0) /\
                      ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
                      ((i:Z)
                       (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                        `i < 2 * k0 + 1` \/ `n0 < i` /\ `i < N0` ->
                        `(access t2 i) = (access t0 i)`)) /\
                      ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))) 
                      t1 result1 Post20)
                  | (right Test6) =>
                      let (result1, Post19) = (exist_1 [result1: unit]
                        (permut t0 t0) /\
                        ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t0 n0 i))) /\
                        ((i:Z)
                         (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                          `i < 2 * k0 + 1` \/ `n0 < i` /\ `i < N0` ->
                          `(access t0 i) = (access t0 i)`)) /\
                        ((v:Z) ((inftree t0 n0 v k0) -> (inftree t0 n0 v k0))) 
                        tt
                        (downheap_po_14 N k n t Pre11 Variant1 N0 k0 n0 t0
                        Pre10 Pre9 j Post1 Test8 j' Post10 Test6)) in
                      (exist_2 [t1: (array N0 Z)][result2: unit]
                      (permut t1 t0) /\
                      ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t1 n0 i))) /\
                      ((i:Z)
                       (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                        `i < 2 * k0 + 1` \/ `n0 < i` /\ `i < N0` ->
                        `(access t1 i) = (access t0 i)`)) /\
                      ((v:Z) ((inftree t0 n0 v k0) -> (inftree t1 n0 v k0))) 
                      t0 result1 Post19) end) in
                (exist_2 [t2: (array N0 Z)][result1: unit](permut t2 t0) /\
                ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
                ((i:Z)
                 (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
                  `n0 < i` /\ `i < N0` -> `(access t2 i) = (access t0 i)`)) /\
                ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))) 
                t1 result0 Post17) in
              (exist_2 [t2: (array N0 Z)][result1: unit](permut t2 t0) /\
              ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
              ((i:Z)
               (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
                `n0 < i` /\ `i < N0` -> `(access t2 i) = (access t0 i)`)) /\
              ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))) 
              t1 result0 Post9)
          | (right Test1) =>
              let (result0, Post8) = (exist_1 [result0: unit]
                (permut t0 t0) /\
                ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t0 n0 i))) /\
                ((i:Z)
                 (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
                  `n0 < i` /\ `i < N0` -> `(access t0 i) = (access t0 i)`)) /\
                ((v:Z) ((inftree t0 n0 v k0) -> (inftree t0 n0 v k0))) 
                tt
                (downheap_po_15 N k n t Pre11 Variant1 N0 k0 n0 t0 Pre10 Pre9
                j Post1 Test1)) in
              (exist_2 [t1: (array N0 Z)][result1: unit](permut t1 t0) /\
              ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t1 n0 i))) /\
              ((i:Z)
               (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
                `n0 < i` /\ `i < N0` -> `(access t1 i) = (access t0 i)`)) /\
              ((v:Z) ((inftree t0 n0 v k0) -> (inftree t1 n0 v k0))) 
              t0 result0 Post8) end) in
        (exist_2 [t2: (array N0 Z)][result0: unit](permut t2 t0) /\
        ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
        ((i:Z)
         (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/ `n0 < i` /\
          `i < N0` -> `(access t2 i) = (access t0 i)`)) /\
        ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))) t1 result
        Post6) `n - k` N k n t (refl_equal ? `n - k`) Pre11).



