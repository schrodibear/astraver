(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.


(* Why obligation from file "quicksort2.mlw", characters 230-234 *)
Lemma swap_po_1 : 
  (i: Z)
  (j: Z)
  (t: (array Z))
  (Pre5: (`0 <= i` /\ `i < (array_length t)`) /\ `0 <= j` /\
         `j < (array_length t)`)
  (Pre4: `0 <= i` /\ `i < (array_length t)`)
  (v: Z)
  (Post3: v = (access t i))
  (Pre2: `0 <= i` /\ `i < (array_length t)`)
  `0 <= j` /\ `j < (array_length t)`.
Proof.
Tauto.
Save.

(* Why obligation from file "quicksort2.mlw", characters 241-250 *)
Lemma swap_po_2 : 
  (i: Z)
  (j: Z)
  (t: (array Z))
  (Pre5: (`0 <= i` /\ `i < (array_length t)`) /\ `0 <= j` /\
         `j < (array_length t)`)
  (Pre4: `0 <= i` /\ `i < (array_length t)`)
  (v: Z)
  (Post3: v = (access t i))
  (Pre2: `0 <= i` /\ `i < (array_length t)`)
  (Pre3: `0 <= j` /\ `j < (array_length t)`)
  (t0: (array Z))
  (Post1: t0 = (store t i (access t j)))
  `0 <= j` /\ `j < (array_length t0)`.
Proof.
Intros; ArraySubst t0.
Save.


(* Why obligation from file "quicksort2.mlw", characters 211-257 *)
Lemma swap_po_3 : 
  (i: Z)
  (j: Z)
  (t: (array Z))
  (Pre5: (`0 <= i` /\ `i < (array_length t)`) /\ `0 <= j` /\
         `j < (array_length t)`)
  (Pre4: `0 <= i` /\ `i < (array_length t)`)
  (v: Z)
  (Post3: v = (access t i))
  (Pre2: `0 <= i` /\ `i < (array_length t)`)
  (Pre3: `0 <= j` /\ `j < (array_length t)`)
  (t0: (array Z))
  (Post1: t0 = (store t i (access t j)))
  (Pre1: `0 <= j` /\ `j < (array_length t0)`)
  (t1: (array Z))
  (Post2: t1 = (store t0 j v))
  (exchange t1 t i j).
Proof.
Intros; Subst t1; Subst t0; Subst v.
Auto with datatypes.
Save.

(* Why obligation from file "quicksort2.mlw", characters 531-535 *)
Lemma quick_rec_po_1 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test6: `l0 < r0`)
  `0 <= l0` /\ `l0 < (array_length t0)`.
Proof.
Auto with *.
Save.

(* Why obligation from file "quicksort2.mlw", characters 903-908 *)
Lemma quick_rec_po_2 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test6: `l0 < r0`)
  (Pre24: `0 <= l0` /\ `l0 < (array_length t0)`)
  (v: Z)
  (Post18: v = (access t0 l0))
  (m: Z)
  (Post17: m = l0)
  (i: Z)
  (Post16: i = `l0 + 1`)
  (Variant3: Z)
  (i1: Z)
  (m1: Z)
  (t1: (array Z))
  (Pre12: Variant3 = `1 + r0 - i1`)
  (Pre11: ((j:Z) (`l0 < j` /\ `j <= m1` -> `(access t1 j) < v`)) /\
          ((j:Z) (`m1 < j` /\ `j < i1` -> `(access t1 j) >= v`)) /\
          (sub_permut l0 r0 t1 t0) /\ `(access t1 l0) = v` /\ (`l0 <= m1` /\
          `m1 < i1`) /\ `i1 <= r0 + 1`)
  (Test5: `i1 <= r0`)
  `0 <= i1` /\ `i1 < (array_length t1)`.
Proof.
Intuition.
ArrayLength.
Save.

(* Why obligation from file "quicksort2.mlw", characters 937-951 *)
Lemma quick_rec_po_3 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test6: `l0 < r0`)
  (Pre24: `0 <= l0` /\ `l0 < (array_length t0)`)
  (v: Z)
  (Post18: v = (access t0 l0))
  (m: Z)
  (Post17: m = l0)
  (i: Z)
  (Post16: i = `l0 + 1`)
  (Variant3: Z)
  (i1: Z)
  (m1: Z)
  (t1: (array Z))
  (Pre12: Variant3 = `1 + r0 - i1`)
  (Pre11: ((j:Z) (`l0 < j` /\ `j <= m1` -> `(access t1 j) < v`)) /\
          ((j:Z) (`m1 < j` /\ `j < i1` -> `(access t1 j) >= v`)) /\
          (sub_permut l0 r0 t1 t0) /\ `(access t1 l0) = v` /\ (`l0 <= m1` /\
          `m1 < i1`) /\ `i1 <= r0 + 1`)
  (Test5: `i1 <= r0`)
  (Pre10: `0 <= i1` /\ `i1 < (array_length t1)`)
  (Test4: `(access t1 i1) < v`)
  (m2: Z)
  (Post13: m2 = `m1 + 1`)
  (`0 <= i1` /\ `i1 < (array_length t1)`) /\ `0 <= m2` /\
  `m2 < (array_length t1)`.
Proof.
Intuition ArrayLength; Omega.
Save.

(* Why obligation from file "quicksort2.mlw", characters 918-955 *)
Lemma quick_rec_po_4 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test6: `l0 < r0`)
  (Pre24: `0 <= l0` /\ `l0 < (array_length t0)`)
  (v: Z)
  (Post18: v = (access t0 l0))
  (m: Z)
  (Post17: m = l0)
  (i: Z)
  (Post16: i = `l0 + 1`)
  (Variant3: Z)
  (i1: Z)
  (m1: Z)
  (t1: (array Z))
  (Pre12: Variant3 = `1 + r0 - i1`)
  (Pre11: ((j:Z) (`l0 < j` /\ `j <= m1` -> `(access t1 j) < v`)) /\
          ((j:Z) (`m1 < j` /\ `j < i1` -> `(access t1 j) >= v`)) /\
          (sub_permut l0 r0 t1 t0) /\ `(access t1 l0) = v` /\ (`l0 <= m1` /\
          `m1 < i1`) /\ `i1 <= r0 + 1`)
  (Test5: `i1 <= r0`)
  (Pre10: `0 <= i1` /\ `i1 < (array_length t1)`)
  (Test4: `(access t1 i1) < v`)
  (m2: Z)
  (Post13: m2 = `m1 + 1`)
  (Pre9: (`0 <= i1` /\ `i1 < (array_length t1)`) /\ `0 <= m2` /\
         `m2 < (array_length t1)`)
  (t2: (array Z))
  (Post30: (exchange t2 t1 i1 m2))
  ((i:Z)
   (i = `i1 + 1` ->
    (((j:Z) (`l0 < j` /\ `j <= m2` -> `(access t2 j) < v`)) /\
    ((j:Z) (`m2 < j` /\ `j < i` -> `(access t2 j) >= v`)) /\
    (sub_permut l0 r0 t2 t0) /\ `(access t2 l0) = v` /\ (`l0 <= m2` /\
    `m2 < i`) /\ `i <= r0 + 1`) /\ (Zwf `0` `1 + r0 - i` `1 + r0 - i1`))).
Proof.
Intuition.
Assert hj : `j < m2` \/ j = m2. Omega. 
Decompose [exchange] Post30. Intuition.
Rewrite H26; Try Omega.
Apply H5; Omega.
Subst j; Rewrite H25; Assumption.
Assert hj : `j < i1` \/ j = i1. Omega. 
Decompose [exchange] Post30. Intuition.
Rewrite H26; Try Omega.
Apply H9; Omega.
Subst j; Rewrite H24. Apply H9; Omega.
Apply sub_permut_trans with t1.
Apply exchange_is_sub_permut with i1 m2; Assumption Orelse Omega.
Assumption.
Decompose [exchange] Post30. Intuition.
Rewrite H24; Omega.
Save.

(* Why obligation from file "quicksort2.mlw", characters 955-955 *)
Lemma quick_rec_po_5 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test6: `l0 < r0`)
  (Pre24: `0 <= l0` /\ `l0 < (array_length t0)`)
  (v: Z)
  (Post18: v = (access t0 l0))
  (m: Z)
  (Post17: m = l0)
  (i: Z)
  (Post16: i = `l0 + 1`)
  (Variant3: Z)
  (i1: Z)
  (m1: Z)
  (t1: (array Z))
  (Pre12: Variant3 = `1 + r0 - i1`)
  (Pre11: ((j:Z) (`l0 < j` /\ `j <= m1` -> `(access t1 j) < v`)) /\
          ((j:Z) (`m1 < j` /\ `j < i1` -> `(access t1 j) >= v`)) /\
          (sub_permut l0 r0 t1 t0) /\ `(access t1 l0) = v` /\ (`l0 <= m1` /\
          `m1 < i1`) /\ `i1 <= r0 + 1`)
  (Test5: `i1 <= r0`)
  (Pre10: `0 <= i1` /\ `i1 < (array_length t1)`)
  (Test3: `(access t1 i1) >= v`)
  ((i:Z)
   (i = `i1 + 1` ->
    (((j:Z) (`l0 < j` /\ `j <= m1` -> `(access t1 j) < v`)) /\
    ((j:Z) (`m1 < j` /\ `j < i` -> `(access t1 j) >= v`)) /\
    (sub_permut l0 r0 t1 t0) /\ `(access t1 l0) = v` /\ (`l0 <= m1` /\
    `m1 < i`) /\ `i <= r0 + 1`) /\ (Zwf `0` `1 + r0 - i` `1 + r0 - i1`))).
Proof.
Intuition.
Assert hj : `j < i1` \/ `j = i1`. Omega. Intuition.
Rewrite H15; Assumption.
Save.

(* Why obligation from file "quicksort2.mlw", characters 654-859 *)
Lemma quick_rec_po_6 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test6: `l0 < r0`)
  (Pre24: `0 <= l0` /\ `l0 < (array_length t0)`)
  (v: Z)
  (Post18: v = (access t0 l0))
  (m: Z)
  (Post17: m = l0)
  (i: Z)
  (Post16: i = `l0 + 1`)
  ((j:Z) (`l0 < j` /\ `j <= m` -> `(access t0 j) < v`)) /\
  ((j:Z) (`m < j` /\ `j < i` -> `(access t0 j) >= v`)) /\
  (sub_permut l0 r0 t0 t0) /\ `(access t0 l0) = v` /\ (`l0 <= m` /\
  `m < i`) /\ `i <= r0 + 1`.
Proof.
Intuition.
Save.

(* Why obligation from file "quicksort2.mlw", characters 998-1011 *)
Lemma quick_rec_po_7 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test6: `l0 < r0`)
  (Pre24: `0 <= l0` /\ `l0 < (array_length t0)`)
  (v: Z)
  (Post18: v = (access t0 l0))
  (m: Z)
  (Post17: m = l0)
  (i: Z)
  (Post16: i = `l0 + 1`)
  (i1: Z)
  (m1: Z)
  (t1: (array Z))
  (Post15: (((j:Z) (`l0 < j` /\ `j <= m1` -> `(access t1 j) < v`)) /\
           ((j:Z) (`m1 < j` /\ `j < i1` -> `(access t1 j) >= v`)) /\
           (sub_permut l0 r0 t1 t0) /\ `(access t1 l0) = v` /\ (`l0 <= m1` /\
           `m1 < i1`) /\ `i1 <= r0 + 1`) /\ `i1 > r0`)
  (`0 <= l0` /\ `l0 < (array_length t1)`) /\ `0 <= m1` /\
  `m1 < (array_length t1)`.
Proof.
Intuition ArrayLength; Omega.
Save.

(* Why obligation from file "quicksort2.mlw", characters 1020-1044 *)
Lemma quick_rec_po_8 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test6: `l0 < r0`)
  (Pre24: `0 <= l0` /\ `l0 < (array_length t0)`)
  (v: Z)
  (Post18: v = (access t0 l0))
  (m: Z)
  (Post17: m = l0)
  (i: Z)
  (Post16: i = `l0 + 1`)
  (i1: Z)
  (m1: Z)
  (t1: (array Z))
  (Post15: (((j:Z) (`l0 < j` /\ `j <= m1` -> `(access t1 j) < v`)) /\
           ((j:Z) (`m1 < j` /\ `j < i1` -> `(access t1 j) >= v`)) /\
           (sub_permut l0 r0 t1 t0) /\ `(access t1 l0) = v` /\ (`l0 <= m1` /\
           `m1 < i1`) /\ `i1 <= r0 + 1`) /\ `i1 > r0`)
  (Pre23: (`0 <= l0` /\ `l0 < (array_length t1)`) /\ `0 <= m1` /\
          `m1 < (array_length t1)`)
  (t2: (array Z))
  (Post32: (exchange t2 t1 l0 m1))
  `0 <= l0` /\ `m1 - 1 < (array_length t2)`.
Proof.
Intuition ArrayLength.
Save.

(* Why obligation from file "quicksort2.mlw", characters 465-1143 *)
Lemma quick_rec_po_9 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test6: `l0 < r0`)
  (Pre24: `0 <= l0` /\ `l0 < (array_length t0)`)
  (v: Z)
  (Post18: v = (access t0 l0))
  (m: Z)
  (Post17: m = l0)
  (i: Z)
  (Post16: i = `l0 + 1`)
  (i1: Z)
  (m1: Z)
  (t1: (array Z))
  (Post15: (((j:Z) (`l0 < j` /\ `j <= m1` -> `(access t1 j) < v`)) /\
           ((j:Z) (`m1 < j` /\ `j < i1` -> `(access t1 j) >= v`)) /\
           (sub_permut l0 r0 t1 t0) /\ `(access t1 l0) = v` /\ (`l0 <= m1` /\
           `m1 < i1`) /\ `i1 <= r0 + 1`) /\ `i1 > r0`)
  (Pre23: (`0 <= l0` /\ `l0 < (array_length t1)`) /\ `0 <= m1` /\
          `m1 < (array_length t1)`)
  (t2: (array Z))
  (Post32: (exchange t2 t1 l0 m1))
  (Pre22: `0 <= l0` /\ `m1 - 1 < (array_length t2)`)
  (Pre16: `0 <= l0` /\ `m1 - 1 < (array_length t2)`)
  (Pre17: `0 <= l0` /\ `m1 - 1 < (array_length t2)`)
  (Zwf `0` `1 + (m1 - 1) - l0` Variant1).
Proof.
Intuition.
Save.

(* Why obligation from file "quicksort2.mlw", characters 1053-1077 *)
Lemma quick_rec_po_10 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test6: `l0 < r0`)
  (Pre24: `0 <= l0` /\ `l0 < (array_length t0)`)
  (v: Z)
  (Post18: v = (access t0 l0))
  (m: Z)
  (Post17: m = l0)
  (i: Z)
  (Post16: i = `l0 + 1`)
  (i1: Z)
  (m1: Z)
  (t1: (array Z))
  (Post15: (((j:Z) (`l0 < j` /\ `j <= m1` -> `(access t1 j) < v`)) /\
           ((j:Z) (`m1 < j` /\ `j < i1` -> `(access t1 j) >= v`)) /\
           (sub_permut l0 r0 t1 t0) /\ `(access t1 l0) = v` /\ (`l0 <= m1` /\
           `m1 < i1`) /\ `i1 <= r0 + 1`) /\ `i1 > r0`)
  (Pre23: (`0 <= l0` /\ `l0 < (array_length t1)`) /\ `0 <= m1` /\
          `m1 < (array_length t1)`)
  (t2: (array Z))
  (Post32: (exchange t2 t1 l0 m1))
  (Pre22: `0 <= l0` /\ `m1 - 1 < (array_length t2)`)
  (t3: (array Z))
  (Post34: (sorted_array t3 l0 `m1 - 1`) /\ (sub_permut l0 `m1 - 1` t3 t2))
  `0 <= m1 + 1` /\ `r0 < (array_length t3)`.
Proof.
Intuition.
Generalize (sub_permut_length H20);
Generalize (exchange_length Post32); 
Generalize (sub_permut_length H10);
Intros; Omega.
Save.

(* Why obligation from file "quicksort2.mlw", characters 465-1143 *)
Lemma quick_rec_po_11 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test6: `l0 < r0`)
  (Pre24: `0 <= l0` /\ `l0 < (array_length t0)`)
  (v: Z)
  (Post18: v = (access t0 l0))
  (m: Z)
  (Post17: m = l0)
  (i: Z)
  (Post16: i = `l0 + 1`)
  (i1: Z)
  (m1: Z)
  (t1: (array Z))
  (Post15: (((j:Z) (`l0 < j` /\ `j <= m1` -> `(access t1 j) < v`)) /\
           ((j:Z) (`m1 < j` /\ `j < i1` -> `(access t1 j) >= v`)) /\
           (sub_permut l0 r0 t1 t0) /\ `(access t1 l0) = v` /\ (`l0 <= m1` /\
           `m1 < i1`) /\ `i1 <= r0 + 1`) /\ `i1 > r0`)
  (Pre23: (`0 <= l0` /\ `l0 < (array_length t1)`) /\ `0 <= m1` /\
          `m1 < (array_length t1)`)
  (t2: (array Z))
  (Post32: (exchange t2 t1 l0 m1))
  (Pre22: `0 <= l0` /\ `m1 - 1 < (array_length t2)`)
  (t3: (array Z))
  (Post34: (sorted_array t3 l0 `m1 - 1`) /\ (sub_permut l0 `m1 - 1` t3 t2))
  (Pre21: `0 <= m1 + 1` /\ `r0 < (array_length t3)`)
  (Pre19: `0 <= m1 + 1` /\ `r0 < (array_length t3)`)
  (Pre20: `0 <= m1 + 1` /\ `r0 < (array_length t3)`)
  (Zwf `0` `1 + r0 - (m1 + 1)` Variant1).
Proof.
Intuition.
Save.

(* Why obligation from file "quicksort2.mlw", characters 594-1086 *)
Lemma quick_rec_po_12 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test6: `l0 < r0`)
  (Pre24: `0 <= l0` /\ `l0 < (array_length t0)`)
  (v: Z)
  (Post18: v = (access t0 l0))
  (m: Z)
  (Post17: m = l0)
  (i: Z)
  (Post16: i = `l0 + 1`)
  (i1: Z)
  (m1: Z)
  (t1: (array Z))
  (Post15: (((j:Z) (`l0 < j` /\ `j <= m1` -> `(access t1 j) < v`)) /\
           ((j:Z) (`m1 < j` /\ `j < i1` -> `(access t1 j) >= v`)) /\
           (sub_permut l0 r0 t1 t0) /\ `(access t1 l0) = v` /\ (`l0 <= m1` /\
           `m1 < i1`) /\ `i1 <= r0 + 1`) /\ `i1 > r0`)
  (Pre23: (`0 <= l0` /\ `l0 < (array_length t1)`) /\ `0 <= m1` /\
          `m1 < (array_length t1)`)
  (t2: (array Z))
  (Post32: (exchange t2 t1 l0 m1))
  (Pre22: `0 <= l0` /\ `m1 - 1 < (array_length t2)`)
  (t3: (array Z))
  (Post34: (sorted_array t3 l0 `m1 - 1`) /\ (sub_permut l0 `m1 - 1` t3 t2))
  (Pre21: `0 <= m1 + 1` /\ `r0 < (array_length t3)`)
  (t4: (array Z))
  (Post36: (sorted_array t4 `m1 + 1` r0) /\ (sub_permut `m1 + 1` r0 t4 t3))
  (sorted_array t4 l0 r0) /\ (sub_permut l0 r0 t4 t0).
Proof.
Intuition.
Unfold sorted_array; Intros.
Assert hx: `x < m1-1` \/ `x = m1-1` \/ x = m1 \/ `m1 < x`. 
Omega. Intuition.
(* x < m0-1 *)
Elim (sub_permut_id H24); Intros.
Unfold array_id in H29.
Rewrite (H29 x). Rewrite (H29 `x+1`). 
Apply H19; Omega. Omega. Omega.
(* x = m0-1 *)
Elim (sub_permut_id H24); Intros.
Unfold array_id in H28.
Rewrite (H28 x). Rewrite (H28 `x+1`). 
Clear H28 H30. Elim (sub_permut_id H20); Intros.
Unfold array_id in H30. Replace `x+1` with m1.
Rewrite (H30 m1). Elim Post32; Intros.
Rewrite H35. Rewrite H13. Clear H34 H35 H36.
Assert hm0 : `m1-1 < (array_length t2)`. Omega.
Rewrite <- (sub_permut_length H20) in hm0.
Generalize (sub_permut_function H20 H1 hm0); Intros.
Elim (H34 x). Clear H34. Intuition.
Elim H34; Intros j [ H1j H2j].
Rewrite H2j.
Assert j = l0 \/ `l0 < j`. Omega. Intuition.
Elim Post32; Intros.
Subst j. Rewrite H44.
Assert `(access t1 m1) < v`.
Apply H9; Omega. Omega.
Elim Post32; Intros.
Rewrite H46; Try Omega.
Assert `(access t1 j) < v`.
Apply H9; Omega. Omega.
Omega. Omega. Omega. Omega. Omega.
(* x = m0 *)
Subst x.
Elim (sub_permut_id H24); Intros.
Unfold array_id in H28.
Rewrite (H28 m1). Clear H28 H29.
Assert hm0 : `0 <= m1+1`. Omega.
Assert hl:(array_length t4)=(array_length t0).
  ArrayLength; Clear H24.
  ArrayLength; Clear H20.
  ArrayLength; Clear Post32.
  ArrayLength.
Rewrite <- hl in H2.
Generalize (sub_permut_function H24 hm0 H2); Intros.
Elim (H28 `m1+1`). Clear H28. Intuition.
Elim H28; Intros j [H1j H2j]. Rewrite H2j.
Clear H28 H29 H2j.
Elim (sub_permut_id H20); Intros.
Unfold array_id in H29.
Rewrite (H29 m1); Try Omega. Rewrite (H29 j); Try Omega.
Elim Post32; Intros.
Rewrite H34.
Rewrite (H35 j); Try Omega.
Rewrite H13.
Apply Zge_le.
Apply H8; Omega. ArrayLength; Clear Post32; ArrayLength. 
Omega. Omega.
(* sub_permut *)
Apply sub_permut_trans with t3.
Apply sub_permut_extension with `m1+1` r0.
Omega. Omega. Assumption.
Apply sub_permut_trans with t2.
Apply sub_permut_extension with l0 `m1-1`.
Omega. Omega. Assumption.
Apply sub_permut_trans with t1.
Apply exchange_is_sub_permut with l0 m1.
Omega. Omega. Assumption.
Assumption.
Save.

(* Why obligation from file "quicksort2.mlw", characters 1086-1086 *)
Lemma quick_rec_po_13 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre27: `0 <= l` /\ `r < (array_length t)`)
  (Variant1: Z)
  (l0: Z)
  (r0: Z)
  (t0: (array Z))
  (Pre26: Variant1 = `1 + r0 - l0`)
  (Pre25: `0 <= l0` /\ `r0 < (array_length t0)`)
  (Test1: `l0 >= r0`)
  (sorted_array t0 l0 r0) /\ (sub_permut l0 r0 t0 t0).
Proof.
Intuition.
Unfold sorted_array; Intros; Omega.
Save.


(* Why obligation from file "quicksort2.mlw", characters 1247-1351 *)
Lemma quicksort_po_1 : 
  (t: (array Z))
  `0 <= 0` /\ `(array_length t) - 1 < (array_length t)`.
Proof.
Intuition Omega.
Save.

(* Why obligation from file "quicksort2.mlw", characters 1247-1351 *)
Lemma quicksort_po_2 : 
  (t: (array Z))
  (Pre1: `0 <= 0` /\ `(array_length t) - 1 < (array_length t)`)
  (t0: (array Z))
  (Post1: (sorted_array t0 `0` `(array_length t) - 1`) /\
          (sub_permut `0` `(array_length t) - 1` t0 t))
  (sorted_array t0 `0` `(array_length t0) - 1`) /\ (permut t0 t).
Proof.
Intuition.
ArrayLength; Assumption.
EAuto.
Save.

