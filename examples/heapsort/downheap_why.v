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

Inductive select_son [t:(array Z); k,n,j:Z] : Prop :=
    select_left_son : 
      `j = 2*k+1` -> (`2*k+2 <= n` -> (Zge #t[j] #t[`2*k+2`])) 
        -> (select_son t k n j)
  | select_right_son :
      `j = 2*k+2` -> `j <= n` -> (Zge #t[j] #t[`2*k+1`]) 
        -> (select_son t k n j).

Implicit Arguments Off.

(* The correctness of downheap requires the two following lemmas *)

Lemma Lemma_1 : (t0,t1,t2:(array Z))
    (n0,k0,j':Z)
    `2*k0+1 <= n0`
 -> (select_son t0 k0 n0 j')
 -> `(access   t0 k0) < (access   t0 j')`
 -> (exchange t1 t0 k0 j')
 -> `0 <= k0 <= n0`
 -> `n0 < (array_length t0)`
 -> ((i:Z)`k0+1 <= i <= n0`->(heap t0 n0 i))
 -> ((i:Z)`j' <= i <= n0`->(heap t2 n0 i))
 -> ((i:Z)
        `0 <= i < j'`\/`j' < i < 2*j'+1`\/`n0 < i < (array_length t0)`
        ->`(access   t2 i) = (access   t1 i)`)
 -> ((v:Z)(inftree t1 n0 v j')->(inftree t2 n0 v j'))
 -> (i:Z)`k0 < i < j'`->(heap t2 n0 i).
Proof.
Intros. Apply heap_cons.
Elim H0; Omega'.
(* branch 2i+1 *)
Intro. Rewrite (H7 i). Rewrite (H7 `2*i+1`).
Decompose [exchange] H2. Rewrite (H16 i). Rewrite (H16 `2*i+1`).
Generalize H10. Elim (H5 i); Intros. Exact (H18 H24).
Omega'. Omega'. Omega'.
Elim H0; Omega'. Omega'. Omega'. Omega'.
Elim H0; Omega'. Elim H0; Omega'. 
Intro. Apply H6; Elim H0; Omega'.
(* branch 2i+2 *)
Intro. Rewrite (H7 i). Rewrite (H7 `2*i+2`).
Decompose [exchange] H2. Rewrite (H16 i). Rewrite (H16 `2*i+2`).
Generalize H10. Elim (H5 i); Intros. Exact (H21 H24).
Omega'. Omega'. Omega'. 
Elim H0; Omega'. Omega'. Omega'. Omega'.
Elim H0; Omega'. Elim H0; Omega'. 
Intro. Apply H6; Elim H0; Omega'.
Save.

Lemma Lemma_2 : (t0,t1,t2:(array Z))
    (n0,k0,j':Z)
    `2*k0+1 <= n0`
 -> (select_son t0 k0 n0 j')
 -> `(access   t0 k0) < (access   t0 j')`
 -> (exchange t1 t0 k0 j')
 -> `0 <= k0 <= n0`
 -> `n0 < (array_length t0)`
 -> ((i:Z)`k0+1 <= i <= n0`->(heap t0 n0 i))
 -> ((i:Z)`j' <= i <= n0`->(heap t2 n0 i))
 -> ((i:Z)
        `0 <= i < j'`\/`j' < i < 2*j'+1`\/`n0 < i < (array_length t0)`
        ->`(access   t2 i) = (access   t1 i)`)
 -> ((v:Z)(inftree t1 n0 v j')->(inftree t2 n0 v j'))
 -> (i:Z)`k0 <= i <= n0`->(heap t2 n0 i).
Proof.
Intros.
Elim (Z_lt_ge_dec i j'); Intro HHi.
Elim (Z_le_lt_eq_dec k0 i); [ Intro HHHi | Intro HHHi | Intuition ].

(* 1. k0 < i < j' *)
Apply (Lemma_1 t0 t1 t2 n0 k0 j'); Assumption Orelse Omega'.

(* 2. k0 = i *)
Apply heap_cons.
Omega'.
(* branch 2i+1 *)
(* t[k] >= t[2k+1] *)
Intro. Elim H0; Intros.
  (* j' = 2k+1 *)
  Rewrite <- HHHi. Rewrite <- H11.
  Rewrite (H7 k0). Decompose [exchange] H2. Rewrite H16.
  Apply Zle_ge. Apply inftree_1 with n:=n0.
  Apply H8.
  Apply inftree_2 with t1:=t0 k:=k0. Omega'. 
  Apply inftree_3.
  Apply H5; Omega'. Assumption. Omega'. Omega'. Omega'.
  (* j' = 2k+2 *)
  Rewrite <- HHHi.
  Rewrite (H7 k0). Decompose [exchange] H2. Rewrite H17.
  Rewrite (H7 `2*k0+1`). Rewrite (H19 `2*k0+1`).
  Omega'. Omega'. Omega'. Omega'. Omega'. Omega'. 
(* (heap t2 n (2k+1)) *)
Intro. Elim H0; Intros.
  (* j' = 2k+1 *)
  Apply H6; Omega'.
  (* j' = 2k+2 *)
  Apply (Lemma_1 t0 t1 t2 n0 k0 j'); Assumption Orelse Omega'.
(* branch 2i+2 *)
(* t[k] >= t[2k+2] *)
Intro. Elim H0; Intros.
  (* j' = 2k+1 *)
  Rewrite <- HHHi.
  Rewrite (H7 k0). Decompose [exchange] H2. Rewrite H16.
  Rewrite (H7 `2*k0+2`). Rewrite (H18 `2*k0+2`).
  Omega'. Omega'. Omega'. Omega'. Omega'. Omega'. 
  (* j' = 2k+2 *)
  Rewrite <- HHHi. Rewrite <- H11.
  Rewrite (H7 k0). Decompose [exchange] H2. Rewrite H17.
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
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (Test5: `j + 1 <= n0`)
  `0 <= j + 1` /\ `j + 1 < (array_length t0)`.
Proof.
Intros; Omega'.
Save.

Lemma downheap_po_2 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (Test5: `j + 1 <= n0`)
  (Pre3: `0 <= j + 1` /\ `j + 1 < (array_length t0)`)
  `0 <= j` /\ `j < (array_length t0)`.
Proof.
Intros; Omega'.
Save.

Lemma downheap_po_3 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (Test5: `j + 1 <= n0`)
  (Test4: `(access t0 j) < (access t0 j + 1)`)
  (select_son t0 k0 n0 `j + 1`).
Proof.
Intros.
Subst j; Rewrite (R11 k0).
Apply select_right_son; 
  [ Reflexivity | Omega' | Rewrite (R11 k0) in Test4; Omega' ].
Save.

Lemma downheap_po_4 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (Test5: `j + 1 <= n0`)
  (Test3: `(access t0 j) >= (access t0 j + 1)`)
  (select_son t0 k0 n0 j).
Proof.
Intros.
Subst j.
Apply select_left_son; 
  [ Reflexivity | Rewrite (R11 k0) in Test3; Intro; Assumption ].
Save.

Lemma downheap_po_5 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (Test2: `j + 1 > n0`)
  (select_son t0 k0 n0 j).
Proof.
Intros.
Subst j.
Apply select_left_son; [ Reflexivity | Intro; Absurd `2*k+2 <= n`; Omega' ].
Save.

Lemma downheap_po_6 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post11: (select_son t0 k0 n0 j'))
  `0 <= j'` /\ `j' < (array_length t0)`.
Proof.
Intros; Elim Post11; Intros; Omega'.
Save.

Lemma downheap_po_7 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post11: (select_son t0 k0 n0 j'))
  (Pre5: `0 <= j'` /\ `j' < (array_length t0)`)
  `0 <= k0` /\ `k0 < (array_length t0)`.
Proof.
Intros; Omega'.
Save.

Lemma downheap_po_8 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post11: (select_son t0 k0 n0 j'))
  (Test7: `(access t0 k0) < (access t0 j')`)
  (`0 <= k0` /\ `k0 < (array_length t0)`) /\ `0 <= j'` /\
  `j' < (array_length t0)`.
Proof.
Intros; Elim Post11; Intros; Omega'.
Save.

Lemma downheap_po_9 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post11: (select_son t0 k0 n0 j'))
  (Test7: `(access t0 k0) < (access t0 j')`)
  (Pre12: (`0 <= k0` /\ `k0 < (array_length t0)`) /\ `0 <= j'` /\
          `j' < (array_length t0)`)
  (t1: (array Z))
  (Post22: (exchange t1 t0 k0 j'))
  (`0 <= j'` /\ `j' <= n0`) /\ `n0 < (array_length t1)` /\
  ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))).
Proof.
Intuition; Try (Elim Post11; SameLength t1 t0; Omega').
Apply heap_id with t := t0.
Apply H7; Elim Post11; Omega'.
Unfold array_id. Intros i' Hi'.
Elim Post22; Intros.
Symmetry; Apply (H18 i'); Elim Post11; Omega'.
Save.

Lemma downheap_po_10 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post11: (select_son t0 k0 n0 j'))
  (Test7: `(access t0 k0) < (access t0 j')`)
  (Pre12: (`0 <= k0` /\ `k0 < (array_length t0)`) /\ `0 <= j'` /\
          `j' < (array_length t0)`)
  (t1: (array Z))
  (Post22: (exchange t1 t0 k0 j'))
  (Pre11: (`0 <= j'` /\ `j' <= n0`) /\ `n0 < (array_length t1)` /\
          ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))))
  (Pre9: (`0 <= j'` /\ `j' <= n0`) /\ `n0 < (array_length t1)` /\
         ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))))
  (Pre10: (`0 <= j'` /\ `j' <= n0`) /\ `n0 < (array_length t1)` /\
          ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))))
  (Zwf `0` `n0 - j'` Variant1).
Proof.
Intros; Unfold Zwf; Decompose [select_son] Post11; Omega'.
Save.

Lemma downheap_po_11 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post11: (select_son t0 k0 n0 j'))
  (Test7: `(access t0 k0) < (access t0 j')`)
  (Pre12: (`0 <= k0` /\ `k0 < (array_length t0)`) /\ `0 <= j'` /\
          `j' < (array_length t0)`)
  (t1: (array Z))
  (Post22: (exchange t1 t0 k0 j'))
  (Pre11: (`0 <= j'` /\ `j' <= n0`) /\ `n0 < (array_length t1)` /\
          ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))))
  (Pre9: (`0 <= j'` /\ `j' <= n0`) /\ `n0 < (array_length t1)` /\
         ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))))
  (Pre10: (`0 <= j'` /\ `j' <= n0`) /\ `n0 < (array_length t1)` /\
          ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))))
  (`0 <= j'` /\ `j' <= n0`) /\ `n0 < (array_length t1)` /\
  ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))).
Proof.
Intuition.
Save.

Lemma downheap_po_12 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post11: (select_son t0 k0 n0 j'))
  (Test7: `(access t0 k0) < (access t0 j')`)
  (Pre12: (`0 <= k0` /\ `k0 < (array_length t0)`) /\ `0 <= j'` /\
          `j' < (array_length t0)`)
  (t1: (array Z))
  (Post22: (exchange t1 t0 k0 j'))
  (Pre11: (`0 <= j'` /\ `j' <= n0`) /\ `n0 < (array_length t1)` /\
          ((i:Z) (`j' + 1 <= i` /\ `i <= n0` -> (heap t1 n0 i))))
  (t2: (array Z))
  (Post24: (permut t2 t1) /\
           ((i:Z) (`j' <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
           ((i:Z)
            (`0 <= i` /\ `i < j'` \/ `j' < i` /\ `i < 2 * j' + 1` \/
             `n0 < i` /\ `i < (array_length t2)` ->
             `(access t2 i) = (access t1 i)`)) /\
           ((v:Z) ((inftree t1 n0 v j') -> (inftree t2 n0 v j'))))
  (permut t2 t0) /\ ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
  ((i:Z)
   (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/ `n0 < i` /\
    `i < (array_length t2)` -> `(access t2 i) = (access t0 i)`)) /\
  ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))).
Proof.
Intuition.

(* permut *)
Apply permut_trans with t' := t1.
Intuition. Apply exchange_is_permut with i:=k0 j:=j'; Assumption.
(* heap *)
Apply (Lemma_2 t0 t1 t2 n0 k0 j'); Assumption Orelse Try Omega'.
SameLength t2 t1. SameLength t1 t0.
Rewrite <- H22; Rewrite <- H18; Assumption.
(* unchanged parts of the array *)
Rewrite (H16 i);
[ Decompose [exchange] Post22; Apply H26 | Idtac ];
Decompose [select_son] Post11; Omega'.
Rewrite (H16 i); 
[ Decompose [exchange] Post22; Apply H26 | Idtac ];
Decompose [select_son] Post11; Omega'.
Rewrite (H16 i); 
[ Decompose [exchange] Post22; Apply H26 | Idtac ];
Decompose [select_son] Post11; SameLength t2 t1; Omega'.
(* inftree *)
Apply inftree_cons.
Split; Assumption.
Rewrite (H16 k0). 
Decompose [exchange] Post22. Rewrite H23. 
Elim Post11; Intros.
  (* j' = 2k+1 *)
  Rewrite H26. Generalize Test8; Rewrite Post2. Case H18; Intros.
  Apply inftree_1 with n:=n0. Auto.
  (* j' = 2k+2 *)
  Generalize H27. Rewrite H26. Case H18; Intros.
  Apply inftree_1 with n:=n0. Auto.
Elim Post11; Intros; Omega'.
  (* branch 2k+1 *)
  Intro. Elim Post11; Intros.
    (* j' = 2k+1 *)
    Rewrite <- H21. Apply H19. 
    Apply inftree_2 with t1:=t0 k:=k0. Omega'. 
    Rewrite H21. Generalize H20. Case H18; Auto.
    Assumption. Omega'. Omega'.
    (* j' = 2k+2 *)
    Apply inftree_trans with v:=#t2[`2*k0+1`].
    Rewrite (H16 `2*k0+1`).
    Decompose [exchange] Post22. Rewrite (H29 `2*k0+1`).
    Generalize H20. Case H18; Intros.
    Apply inftree_1 with n:=n0. Auto.
    Omega'. Omega'. Omega'. Omega'.
    Apply inftree_3.
    Apply (Lemma_2 t0 t1 t2 n0 k0 j'); Assumption Orelse Try Omega'.
    SameLength t2 t1. SameLength t1 t0.
    Rewrite <- H25; Rewrite <- H24; Assumption.

  (* branch 2k+2 *)
  Intro. Elim Post11; Intros.
    (* j' = 2k+1 *)
    Apply inftree_trans with v:=#t2[`2*k0+2`].
    Rewrite (H16 `2*k0+2`).
    Decompose [exchange] Post22. Rewrite (H28 `2*k0+2`).
    Generalize H20. Case H18; Intros.
    Apply inftree_1 with n:=n0. Auto.
    Omega'. Omega'. Omega'. Omega'.
    Apply inftree_3.
    Apply H17; Omega'.
    (* j' = 2k+2 *)
    Rewrite <- H21. Apply H19. 
    Apply inftree_2 with t1:=t0 k:=k0. Omega'. 
    Rewrite H21. Generalize H20. Case H18; Auto.
    Assumption. Omega'. Omega'.
Save.

Lemma downheap_po_13 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test8: `j <= n0`)
  (j': Z)
  (Post11: (select_son t0 k0 n0 j'))
  (Test6: `(access t0 k0) >= (access t0 j')`)
  (permut t0 t0) /\ ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t0 n0 i))) /\
  ((i:Z)
   (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/ `n0 < i` /\
    `i < (array_length t0)` -> `(access t0 i) = (access t0 i)`)) /\
  ((v:Z) ((inftree t0 n0 v k0) -> (inftree t0 n0 v k0))).
Proof.
Intuition.
Elim (Z_le_lt_eq_dec k0 i); [ Intro HHHi | Intro HHHi | Intuition ].
(* k0 < i *)
Apply H7; Omega'.
(* k0 = i *)
Rewrite <- HHHi. Apply heap_cons.
Omega'.
Intro. Elim Post11; Intros.
Rewrite <- H10. Assumption. Omega'.
Intro. Apply H7; Omega'.
Intro. Elim Post11; Intros.
Omega'. Rewrite <- H10. Assumption.
Intro. Apply H7; Omega'.
Save.

Lemma downheap_po_14 : 
  (k: Z)
  (n: Z)
  (t: (array Z))
  (Pre15: (`0 <= k` /\ `k <= n`) /\ `n < (array_length t)` /\
          ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
  (Variant1: Z)
  (k0: Z)
  (n0: Z)
  (t0: (array Z))
  (Pre14: Variant1 = `n0 - k0`)
  (Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
  (j: Z)
  (Post2: j = `2 * k0 + 1`)
  (Test1: `j > n0`)
  (permut t0 t0) /\ ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t0 n0 i))) /\
  ((i:Z)
   (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/ `n0 < i` /\
    `i < (array_length t0)` -> `(access t0 i) = (access t0 i)`)) /\
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
  [k: Z; n: Z; t: (array Z); Pre15: (`0 <= k` /\ `k <= n`) /\
   `n < (array_length t)` /\
   ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i)))]
    (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`) [Variant1: Z]
      (k0: Z)(n0: Z)(t0: (array Z))(_: Variant1 = `n0 - k0`)
      (_0: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
      ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
      (sig_2 (array Z) unit [t1: (array Z)][result: unit]((permut t1 t0) /\
       ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t1 n0 i))) /\
       ((i:Z)
        (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/ `n0 < i` /\
         `i < (array_length t1)` -> `(access t1 i) = (access t0 i)`)) /\
       ((v:Z) ((inftree t0 n0 v k0) -> (inftree t1 n0 v k0)))))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (k0: Z)(n0: Z)(t0: (array Z))(_: Variant2 = `n0 - k0`)
       (_0: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
       ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
       (sig_2 (array Z) unit [t1: (array Z)][result: unit]((permut t1 t0) /\
        ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t1 n0 i))) /\
        ((i:Z)
         (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/ `n0 < i` /\
          `i < (array_length t1)` -> `(access t1 i) = (access t0 i)`)) /\
        ((v:Z) ((inftree t0 n0 v k0) -> (inftree t1 n0 v k0)))));
       k0: Z; n0: Z; t0: (array Z); Pre14: Variant1 = `n0 - k0`;
       Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
       ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i)))]
        let (j, Post2) = (exist_1 [result: Z]
          result = `2 * k0 + 1` `2 * k0 + 1` (refl_equal ? `2 * k0 + 1`)) in
        let (t1, result, Post7) =
          let (result, Bool8) =
            let (result1, Post8) = (Z_le_gt_bool j n0) in
            (exist_1 [result2: bool]
            (if result2 then `j <= n0` else `j > n0`) result1 Post8) in
          (Cases (btest [result:bool](if result then `j <= n0` else `j > n0`)
                  result Bool8) of
          | (left Test8) =>
              let (t1, result0, Post10) =
                let (j', Post11) =
                  let (result0, Bool6) =
                    let (result2, Post12) = (Z_le_gt_bool `j + 1` n0) in
                    (exist_1 [result3: bool]
                    (if result3 then `j + 1 <= n0` else `j + 1 > n0`) 
                    result2 Post12) in
                  (Cases (btest
                          [result0:bool](if result0 then `j + 1 <= n0`
                                         else `j + 1 > n0`)
                          result0 Bool6) of
                  | (left Test5) =>
                      let (result1, Post14) =
                        let (result1, Bool5) =
                          let Pre3 =
                            (downheap_po_1 k n t Pre15 Variant1 k0 n0 t0
                            Pre14 Pre13 j Post2 Test8 Test5) in
                          let result2 =
                            let Pre2 =
                              (downheap_po_2 k n t Pre15 Variant1 k0 n0 t0
                              Pre14 Pre13 j Post2 Test8 Test5 Pre3) in
                            (Z_lt_ge_bool (access t0 j)) in
                          let (result3, Post15) =
                            (result2 (access t0 `j + 1`)) in
                          (exist_1 [result4: bool]
                          (if result4
                           then `(access t0 j) < (access t0 j + 1)`
                           else `(access t0 j) >= (access t0 j + 1)`) 
                          result3 Post15) in
                        (Cases (btest
                                [result1:bool](if result1
                                               then `(access t0 j) <
                                                     (access t0 j + 1)`
                                               else `(access t0 j) >=
                                                     (access t0 j + 1)`)
                                result1 Bool5) of
                        | (left Test4) =>
                            let (result2, Post17) = (exist_1 [result2: Z]
                              (select_son t0 k0 n0 result2) `j + 1`
                              (downheap_po_3 k n t Pre15 Variant1 k0 n0 t0
                              Pre14 Pre13 j Post2 Test8 Test5 Test4)) in
                            (exist_1 [result3: Z]
                            (select_son t0 k0 n0 result3) result2 Post17)
                        | (right Test3) =>
                            let (result2, Post16) = (exist_1 [result2: Z]
                              (select_son t0 k0 n0 result2) j
                              (downheap_po_4 k n t Pre15 Variant1 k0 n0 t0
                              Pre14 Pre13 j Post2 Test8 Test5 Test3)) in
                            (exist_1 [result3: Z]
                            (select_son t0 k0 n0 result3) result2 Post16) end) in
                      (exist_1 [result2: Z]
                      (select_son t0 k0 n0 result2) result1 Post14)
                  | (right Test2) =>
                      let (result1, Post13) = (exist_1 [result1: Z]
                        (select_son t0 k0 n0 result1) j
                        (downheap_po_5 k n t Pre15 Variant1 k0 n0 t0 Pre14
                        Pre13 j Post2 Test8 Test2)) in
                      (exist_1 [result2: Z]
                      (select_son t0 k0 n0 result2) result1 Post13) end) in
                let (t1, result0, Post18) =
                  let (result0, Bool7) =
                    let Pre5 =
                      (downheap_po_6 k n t Pre15 Variant1 k0 n0 t0 Pre14
                      Pre13 j Post2 Test8 j' Post11) in
                    let result1 =
                      let Pre4 =
                        (downheap_po_7 k n t Pre15 Variant1 k0 n0 t0 Pre14
                        Pre13 j Post2 Test8 j' Post11 Pre5) in
                      (Z_lt_ge_bool (access t0 k0)) in
                    let (result2, Post19) = (result1 (access t0 j')) in
                    (exist_1 [result3: bool]
                    (if result3 then `(access t0 k0) < (access t0 j')`
                     else `(access t0 k0) >= (access t0 j')`) result2
                    Post19) in
                  (Cases (btest
                          [result0:bool](if result0
                                         then `(access t0 k0) <
                                               (access t0 j')`
                                         else `(access t0 k0) >=
                                               (access t0 j')`)
                          result0 Bool7) of
                  | (left Test7) =>
                      let (t1, result1, Post21) =
                        let Pre12 =
                          (downheap_po_8 k n t Pre15 Variant1 k0 n0 t0 Pre14
                          Pre13 j Post2 Test8 j' Post11 Test7) in
                        let (t1, result1, Post22) =
                          let Pre6 = Pre12 in
                          let Pre7 = Pre6 in
                          let (t1, result3, Post23) = (swap k0 j' t0 Pre6) in
                          (exist_2 [t2: (array Z)][result4: unit]
                          (exchange t2 t0 k0 j') t1 result3 Post23) in
                        let Pre11 =
                          (downheap_po_9 k n t Pre15 Variant1 k0 n0 t0 Pre14
                          Pre13 j Post2 Test8 j' Post11 Test7 Pre12 t1
                          Post22) in
                        let (t2, result2, Post24) =
                          let Pre9 = Pre11 in
                          let Pre10 = Pre9 in
                          let (t2, result4, Post25) =
                            ((wf1 `n0 - j'`)
                              (downheap_po_10 k n t Pre15 Variant1 k0 n0 t0
                              Pre14 Pre13 j Post2 Test8 j' Post11 Test7 Pre12
                              t1 Post22 Pre11 Pre9 Pre10) j' n0 t1
                              (refl_equal ? `n0 - j'`)
                              (downheap_po_11 k n t Pre15 Variant1 k0 n0 t0
                              Pre14 Pre13 j Post2 Test8 j' Post11 Test7 Pre12
                              t1 Post22 Pre11 Pre9 Pre10)) in
                          (exist_2 [t3: (array Z)][result5: unit]
                          (permut t3 t1) /\
                          ((i:Z) (`j' <= i` /\ `i <= n0` -> (heap t3 n0 i))) /\
                          ((i:Z)
                           (`0 <= i` /\ `i < j'` \/ `j' < i` /\
                            `i < 2 * j' + 1` \/ `n0 < i` /\
                            `i < (array_length t3)` ->
                            `(access t3 i) = (access t1 i)`)) /\
                          ((v:Z)
                           ((inftree t1 n0 v j') -> (inftree t3 n0 v j'))) 
                          t2 result4 Post25) in
                        (exist_2 [t3: (array Z)][result3: unit]
                        (permut t3 t0) /\
                        ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t3 n0 i))) /\
                        ((i:Z)
                         (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                          `i < 2 * k0 + 1` \/ `n0 < i` /\
                          `i < (array_length t3)` ->
                          `(access t3 i) = (access t0 i)`)) /\
                        ((v:Z) ((inftree t0 n0 v k0) -> (inftree t3 n0 v k0))) 
                        t2 result2
                        (downheap_po_12 k n t Pre15 Variant1 k0 n0 t0 Pre14
                        Pre13 j Post2 Test8 j' Post11 Test7 Pre12 t1 Post22
                        Pre11 t2 Post24)) in
                      (exist_2 [t2: (array Z)][result2: unit]
                      (permut t2 t0) /\
                      ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
                      ((i:Z)
                       (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                        `i < 2 * k0 + 1` \/ `n0 < i` /\
                        `i < (array_length t2)` ->
                        `(access t2 i) = (access t0 i)`)) /\
                      ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))) 
                      t1 result1 Post21)
                  | (right Test6) =>
                      let (result1, Post20) = (exist_1 [result1: unit]
                        (permut t0 t0) /\
                        ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t0 n0 i))) /\
                        ((i:Z)
                         (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                          `i < 2 * k0 + 1` \/ `n0 < i` /\
                          `i < (array_length t0)` ->
                          `(access t0 i) = (access t0 i)`)) /\
                        ((v:Z) ((inftree t0 n0 v k0) -> (inftree t0 n0 v k0))) 
                        tt
                        (downheap_po_13 k n t Pre15 Variant1 k0 n0 t0 Pre14
                        Pre13 j Post2 Test8 j' Post11 Test6)) in
                      (exist_2 [t1: (array Z)][result2: unit]
                      (permut t1 t0) /\
                      ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t1 n0 i))) /\
                      ((i:Z)
                       (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                        `i < 2 * k0 + 1` \/ `n0 < i` /\
                        `i < (array_length t1)` ->
                        `(access t1 i) = (access t0 i)`)) /\
                      ((v:Z) ((inftree t0 n0 v k0) -> (inftree t1 n0 v k0))) 
                      t0 result1 Post20) end) in
                (exist_2 [t2: (array Z)][result1: unit](permut t2 t0) /\
                ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
                ((i:Z)
                 (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
                  `n0 < i` /\ `i < (array_length t2)` ->
                  `(access t2 i) = (access t0 i)`)) /\
                ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))) 
                t1 result0 Post18) in
              (exist_2 [t2: (array Z)][result1: unit](permut t2 t0) /\
              ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
              ((i:Z)
               (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
                `n0 < i` /\ `i < (array_length t2)` ->
                `(access t2 i) = (access t0 i)`)) /\
              ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))) 
              t1 result0 Post10)
          | (right Test1) =>
              let (result0, Post9) = (exist_1 [result0: unit]
                (permut t0 t0) /\
                ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t0 n0 i))) /\
                ((i:Z)
                 (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
                  `n0 < i` /\ `i < (array_length t0)` ->
                  `(access t0 i) = (access t0 i)`)) /\
                ((v:Z) ((inftree t0 n0 v k0) -> (inftree t0 n0 v k0))) 
                tt
                (downheap_po_14 k n t Pre15 Variant1 k0 n0 t0 Pre14 Pre13 j
                Post2 Test1)) in
              (exist_2 [t1: (array Z)][result1: unit](permut t1 t0) /\
              ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t1 n0 i))) /\
              ((i:Z)
               (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
                `n0 < i` /\ `i < (array_length t1)` ->
                `(access t1 i) = (access t0 i)`)) /\
              ((v:Z) ((inftree t0 n0 v k0) -> (inftree t1 n0 v k0))) 
              t0 result0 Post9) end) in
        (exist_2 [t2: (array Z)][result0: unit](permut t2 t0) /\
        ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
        ((i:Z)
         (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/ `n0 < i` /\
          `i < (array_length t2)` -> `(access t2 i) = (access t0 i)`)) /\
        ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))) t1 result
        Post7) `n - k` k n t (refl_equal ? `n - k`) Pre15).



