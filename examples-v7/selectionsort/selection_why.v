(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Omega.


(* Why obligation from file "selection.mlw", characters 804-809 *)
Lemma selection_po_1 : 
  (t: (array Z))
  (Pre19: `(array_length t) >= 1`)
  (i: Z)
  (Post11: i = `0`)
  (Variant1: Z)
  (i1: Z)
  (t0: (array Z))
  (Pre18: Variant1 = `(array_length t0) - i1`)
  (Pre17: (`0 <= i1` /\ `i1 <= (array_length t0) - 1`) /\
          (sorted_array t0 `0` `i1 - 1`) /\ (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i1` ->
            ((l:Z)
             (`i1 <= l` /\ `l < (array_length t0)` ->
              `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i1 < (array_length t0) - 1`)
  (min: Z)
  (Post8: min = i1)
  (j: Z)
  (Post7: j = `i1 + 1`)
  (Variant3: Z)
  (j1: Z)
  (min1: Z)
  (Pre12: Variant3 = `(array_length t0) - j1`)
  (Pre11: (`i1 + 1 <= j1` /\ `j1 <= (array_length t0)`) /\ (`i1 <= min1` /\
          `min1 < (array_length t0)`) /\
          ((k:Z)
           (`i1 <= k` /\ `k < j1` -> `(access t0 min1) <= (access t0 k)`)))
  (Test5: `j1 < (array_length t0)`)
  `0 <= j1` /\ `j1 < (array_length t0)`.
Proof.
Auto with *.
Save.

(* Why obligation from file "selection.mlw", characters 812-819 *)
Lemma selection_po_2 : 
  (t: (array Z))
  (Pre19: `(array_length t) >= 1`)
  (i: Z)
  (Post11: i = `0`)
  (Variant1: Z)
  (i1: Z)
  (t0: (array Z))
  (Pre18: Variant1 = `(array_length t0) - i1`)
  (Pre17: (`0 <= i1` /\ `i1 <= (array_length t0) - 1`) /\
          (sorted_array t0 `0` `i1 - 1`) /\ (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i1` ->
            ((l:Z)
             (`i1 <= l` /\ `l < (array_length t0)` ->
              `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i1 < (array_length t0) - 1`)
  (min: Z)
  (Post8: min = i1)
  (j: Z)
  (Post7: j = `i1 + 1`)
  (Variant3: Z)
  (j1: Z)
  (min1: Z)
  (Pre12: Variant3 = `(array_length t0) - j1`)
  (Pre11: (`i1 + 1 <= j1` /\ `j1 <= (array_length t0)`) /\ (`i1 <= min1` /\
          `min1 < (array_length t0)`) /\
          ((k:Z)
           (`i1 <= k` /\ `k < j1` -> `(access t0 min1) <= (access t0 k)`)))
  (Test5: `j1 < (array_length t0)`)
  (Pre9: `0 <= j1` /\ `j1 < (array_length t0)`)
  `0 <= min1` /\ `min1 < (array_length t0)`.
Proof.
Intuition.
Save.

(* Why obligation from file "selection.mlw", characters 825-834 *)
Lemma selection_po_3 : 
  (t: (array Z))
  (Pre19: `(array_length t) >= 1`)
  (i: Z)
  (Post11: i = `0`)
  (Variant1: Z)
  (i1: Z)
  (t0: (array Z))
  (Pre18: Variant1 = `(array_length t0) - i1`)
  (Pre17: (`0 <= i1` /\ `i1 <= (array_length t0) - 1`) /\
          (sorted_array t0 `0` `i1 - 1`) /\ (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i1` ->
            ((l:Z)
             (`i1 <= l` /\ `l < (array_length t0)` ->
              `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i1 < (array_length t0) - 1`)
  (min: Z)
  (Post8: min = i1)
  (j: Z)
  (Post7: j = `i1 + 1`)
  (Variant3: Z)
  (j1: Z)
  (min1: Z)
  (Pre12: Variant3 = `(array_length t0) - j1`)
  (Pre11: (`i1 + 1 <= j1` /\ `j1 <= (array_length t0)`) /\ (`i1 <= min1` /\
          `min1 < (array_length t0)`) /\
          ((k:Z)
           (`i1 <= k` /\ `k < j1` -> `(access t0 min1) <= (access t0 k)`)))
  (Test5: `j1 < (array_length t0)`)
  (Pre9: `0 <= j1` /\ `j1 < (array_length t0)`)
  (Pre10: `0 <= min1` /\ `min1 < (array_length t0)`)
  (Test4: `(access t0 j1) < (access t0 min1)`)
  (min2: Z)
  (Post1: min2 = j1)
  ((j:Z)
   (j = `j1 + 1` -> ((`i1 + 1 <= j` /\ `j <= (array_length t0)`) /\
    (`i1 <= min2` /\ `min2 < (array_length t0)`) /\
    ((k:Z) (`i1 <= k` /\ `k < j` -> `(access t0 min2) <= (access t0 k)`))) /\
    (Zwf `0` `(array_length t0) - j` `(array_length t0) - j1`))).
Proof.
Intuition.
Assert h: `k<j1` \/ `k=j1`. Omega. Intuition.
Apply Zle_trans with (access t0 min1).
Subst min2; Omega.
Apply H12; Omega.
Subst min2 k; Omega.
Save.

(* Why obligation from file "selection.mlw", characters 834-834 *)
Lemma selection_po_4 : 
  (t: (array Z))
  (Pre19: `(array_length t) >= 1`)
  (i: Z)
  (Post11: i = `0`)
  (Variant1: Z)
  (i1: Z)
  (t0: (array Z))
  (Pre18: Variant1 = `(array_length t0) - i1`)
  (Pre17: (`0 <= i1` /\ `i1 <= (array_length t0) - 1`) /\
          (sorted_array t0 `0` `i1 - 1`) /\ (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i1` ->
            ((l:Z)
             (`i1 <= l` /\ `l < (array_length t0)` ->
              `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i1 < (array_length t0) - 1`)
  (min: Z)
  (Post8: min = i1)
  (j: Z)
  (Post7: j = `i1 + 1`)
  (Variant3: Z)
  (j1: Z)
  (min1: Z)
  (Pre12: Variant3 = `(array_length t0) - j1`)
  (Pre11: (`i1 + 1 <= j1` /\ `j1 <= (array_length t0)`) /\ (`i1 <= min1` /\
          `min1 < (array_length t0)`) /\
          ((k:Z)
           (`i1 <= k` /\ `k < j1` -> `(access t0 min1) <= (access t0 k)`)))
  (Test5: `j1 < (array_length t0)`)
  (Pre9: `0 <= j1` /\ `j1 < (array_length t0)`)
  (Pre10: `0 <= min1` /\ `min1 < (array_length t0)`)
  (Test3: `(access t0 j1) >= (access t0 min1)`)
  ((j:Z)
   (j = `j1 + 1` -> ((`i1 + 1 <= j` /\ `j <= (array_length t0)`) /\
    (`i1 <= min1` /\ `min1 < (array_length t0)`) /\
    ((k:Z) (`i1 <= k` /\ `k < j` -> `(access t0 min1) <= (access t0 k)`))) /\
    (Zwf `0` `(array_length t0) - j` `(array_length t0) - j1`))).
Proof.
Intuition.
Assert h: `k<j1` \/ `k=j1`. Omega. Intuition.
Subst k; Omega.
Save.

(* Why obligation from file "selection.mlw", characters 619-755 *)
Lemma selection_po_5 : 
  (t: (array Z))
  (Pre19: `(array_length t) >= 1`)
  (i: Z)
  (Post11: i = `0`)
  (Variant1: Z)
  (i1: Z)
  (t0: (array Z))
  (Pre18: Variant1 = `(array_length t0) - i1`)
  (Pre17: (`0 <= i1` /\ `i1 <= (array_length t0) - 1`) /\
          (sorted_array t0 `0` `i1 - 1`) /\ (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i1` ->
            ((l:Z)
             (`i1 <= l` /\ `l < (array_length t0)` ->
              `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i1 < (array_length t0) - 1`)
  (min: Z)
  (Post8: min = i1)
  (j: Z)
  (Post7: j = `i1 + 1`)
  (`i1 + 1 <= j` /\ `j <= (array_length t0)`) /\ (`i1 <= min` /\
  `min < (array_length t0)`) /\
  ((k:Z) (`i1 <= k` /\ `k < j` -> `(access t0 min) <= (access t0 k)`)).
Proof.
Intuition.
Assert h:`k=i1`. Omega.
Subst min k; Omega.
Save.

(* Why obligation from file "selection.mlw", characters 898-905 *)
Lemma selection_po_6 : 
  (t: (array Z))
  (Pre19: `(array_length t) >= 1`)
  (i: Z)
  (Post11: i = `0`)
  (Variant1: Z)
  (i1: Z)
  (t0: (array Z))
  (Pre18: Variant1 = `(array_length t0) - i1`)
  (Pre17: (`0 <= i1` /\ `i1 <= (array_length t0) - 1`) /\
          (sorted_array t0 `0` `i1 - 1`) /\ (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i1` ->
            ((l:Z)
             (`i1 <= l` /\ `l < (array_length t0)` ->
              `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i1 < (array_length t0) - 1`)
  (min: Z)
  (Post8: min = i1)
  (j: Z)
  (Post7: j = `i1 + 1`)
  (j1: Z)
  (min1: Z)
  (Post3: ((`i1 + 1 <= j1` /\ `j1 <= (array_length t0)`) /\ (`i1 <= min1` /\
          `min1 < (array_length t0)`) /\
          ((k:Z)
           (`i1 <= k` /\ `k < j1` -> `(access t0 min1) <= (access t0 k)`))) /\
          `j1 >= (array_length t0)`)
  `0 <= min1` /\ `min1 < (array_length t0)`.
Proof.
Intuition.
Save.

(* Why obligation from file "selection.mlw", characters 926-931 *)
Lemma selection_po_7 : 
  (t: (array Z))
  (Pre19: `(array_length t) >= 1`)
  (i: Z)
  (Post11: i = `0`)
  (Variant1: Z)
  (i1: Z)
  (t0: (array Z))
  (Pre18: Variant1 = `(array_length t0) - i1`)
  (Pre17: (`0 <= i1` /\ `i1 <= (array_length t0) - 1`) /\
          (sorted_array t0 `0` `i1 - 1`) /\ (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i1` ->
            ((l:Z)
             (`i1 <= l` /\ `l < (array_length t0)` ->
              `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i1 < (array_length t0) - 1`)
  (min: Z)
  (Post8: min = i1)
  (j: Z)
  (Post7: j = `i1 + 1`)
  (j1: Z)
  (min1: Z)
  (Post3: ((`i1 + 1 <= j1` /\ `j1 <= (array_length t0)`) /\ (`i1 <= min1` /\
          `min1 < (array_length t0)`) /\
          ((k:Z)
           (`i1 <= k` /\ `k < j1` -> `(access t0 min1) <= (access t0 k)`))) /\
          `j1 >= (array_length t0)`)
  (Pre16: `0 <= min1` /\ `min1 < (array_length t0)`)
  (w: Z)
  (Post6: w = (access t0 min1))
  (Pre14: `0 <= min1` /\ `min1 < (array_length t0)`)
  `0 <= i1` /\ `i1 < (array_length t0)`.
Proof.
Intuition.
Save.

(* Why obligation from file "selection.mlw", characters 933-943 *)
Lemma selection_po_8 : 
  (t: (array Z))
  (Pre19: `(array_length t) >= 1`)
  (i: Z)
  (Post11: i = `0`)
  (Variant1: Z)
  (i1: Z)
  (t0: (array Z))
  (Pre18: Variant1 = `(array_length t0) - i1`)
  (Pre17: (`0 <= i1` /\ `i1 <= (array_length t0) - 1`) /\
          (sorted_array t0 `0` `i1 - 1`) /\ (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i1` ->
            ((l:Z)
             (`i1 <= l` /\ `l < (array_length t0)` ->
              `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i1 < (array_length t0) - 1`)
  (min: Z)
  (Post8: min = i1)
  (j: Z)
  (Post7: j = `i1 + 1`)
  (j1: Z)
  (min1: Z)
  (Post3: ((`i1 + 1 <= j1` /\ `j1 <= (array_length t0)`) /\ (`i1 <= min1` /\
          `min1 < (array_length t0)`) /\
          ((k:Z)
           (`i1 <= k` /\ `k < j1` -> `(access t0 min1) <= (access t0 k)`))) /\
          `j1 >= (array_length t0)`)
  (Pre16: `0 <= min1` /\ `min1 < (array_length t0)`)
  (w: Z)
  (Post6: w = (access t0 min1))
  (Pre14: `0 <= min1` /\ `min1 < (array_length t0)`)
  (Pre15: `0 <= i1` /\ `i1 < (array_length t0)`)
  (t1: (array Z))
  (Post4: t1 = (store t0 min1 (access t0 i1)))
  `0 <= i1` /\ `i1 < (array_length t1)`.
Proof.
Intuition.
ArraySubst t1.
Save.

(* Why obligation from file "selection.mlw", characters 909-947 *)
Lemma selection_po_9 : 
  (t: (array Z))
  (Pre19: `(array_length t) >= 1`)
  (i: Z)
  (Post11: i = `0`)
  (Variant1: Z)
  (i1: Z)
  (t0: (array Z))
  (Pre18: Variant1 = `(array_length t0) - i1`)
  (Pre17: (`0 <= i1` /\ `i1 <= (array_length t0) - 1`) /\
          (sorted_array t0 `0` `i1 - 1`) /\ (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i1` ->
            ((l:Z)
             (`i1 <= l` /\ `l < (array_length t0)` ->
              `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i1 < (array_length t0) - 1`)
  (min: Z)
  (Post8: min = i1)
  (j: Z)
  (Post7: j = `i1 + 1`)
  (j1: Z)
  (min1: Z)
  (Post3: ((`i1 + 1 <= j1` /\ `j1 <= (array_length t0)`) /\ (`i1 <= min1` /\
          `min1 < (array_length t0)`) /\
          ((k:Z)
           (`i1 <= k` /\ `k < j1` -> `(access t0 min1) <= (access t0 k)`))) /\
          `j1 >= (array_length t0)`)
  (Pre16: `0 <= min1` /\ `min1 < (array_length t0)`)
  (w: Z)
  (Post6: w = (access t0 min1))
  (Pre14: `0 <= min1` /\ `min1 < (array_length t0)`)
  (Pre15: `0 <= i1` /\ `i1 < (array_length t0)`)
  (t1: (array Z))
  (Post4: t1 = (store t0 min1 (access t0 i1)))
  (Pre13: `0 <= i1` /\ `i1 < (array_length t1)`)
  (t2: (array Z))
  (Post5: t2 = (store t1 i1 w))
  ((i:Z)
   (i = `i1 + 1` -> ((`0 <= i` /\ `i <= (array_length t2) - 1`) /\
    (sorted_array t2 `0` `i - 1`) /\ (permut t2 t) /\
    ((k:Z)
     (`0 <= k` /\ `k < i` ->
      ((l:Z)
       (`i <= l` /\ `l < (array_length t2)` ->
        `(access t2 k) <= (access t2 l)`))))) /\
    (Zwf `0` `(array_length t2) - i` `(array_length t0) - i1`))).
Proof.
Intuition.
ArraySubst t2.
ArraySubst t1.
Assert h: `i1=0` \/ `0<i1`. Omega. Intuition.
Replace `i0-1` with `0`.
Unfold sorted_array; Intros; Omega.
Omega.
Replace `i0-1` with `(i1-1)+1`.
Apply right_extension.
Omega.
ArraySubst t2.
ArraySubst t1.
Apply sorted_array_id with t0.
Assumption.
Unfold array_id; Intros.
Subst t2; Do 2 AccessOther.
Replace `i1-1+1` with i1.
Subst t2 t1; Do 2 AccessOther.
Subst w.
Apply H4; Omega.
Omega.
Omega.
Apply permut_trans with t0.
Subst t2; Subst t1; Subst w.
Apply exchange_is_permut with min1 i1; Auto with *.
Assumption.
Assert h:`k=i1` \/ `k<i1`. Omega. Intuition.
Subst k.
Subst t2; Simpl in H23.
AccessSame.
AccessOther.
Subst t1; Simpl in H23.
Assert h:`l=min1` \/ `min1<>l`. Omega. Intuition.
Subst l; AccessSame.
Subst w; Apply H11; Omega.
AccessOther.
Subst w; Apply H11; Try Omega.
Subst t2; Simpl in H23. AccessOther.
AccessOther.
Subst t1; Simpl in H23.
Assert h:`l=min1` \/ `min1<>l`. Omega. Intuition.
Subst l; AccessSame.
AccessOther.
Apply H4; Omega.
AccessOther.
AccessOther.
Apply H4; Omega.
Subst t2 t1; Simpl; Unfold Zwf; Omega.
Save.

(* Why obligation from file "selection.mlw", characters 232-424 *)
Lemma selection_po_10 : 
  (t: (array Z))
  (Pre19: `(array_length t) >= 1`)
  (i: Z)
  (Post11: i = `0`)
  (`0 <= i` /\ `i <= (array_length t) - 1`) /\
  (sorted_array t `0` `i - 1`) /\ (permut t t) /\
  ((k:Z)
   (`0 <= k` /\ `k < i` ->
    ((l:Z)
     (`i <= l` /\ `l < (array_length t)` -> `(access t k) <= (access t l)`)))).
Proof.
Intuition.
Unfold sorted_array; Intros; Omega.
Save.

(* Why obligation from file "selection.mlw", characters 120-985 *)
Lemma selection_po_11 : 
  (t: (array Z))
  (Pre19: `(array_length t) >= 1`)
  (i: Z)
  (Post11: i = `0`)
  (i1: Z)
  (t0: (array Z))
  (Post10: ((`0 <= i1` /\ `i1 <= (array_length t0) - 1`) /\
           (sorted_array t0 `0` `i1 - 1`) /\ (permut t0 t) /\
           ((k:Z)
            (`0 <= k` /\ `k < i1` ->
             ((l:Z)
              (`i1 <= l` /\ `l < (array_length t0)` ->
               `(access t0 k) <= (access t0 l)`))))) /\
           `i1 >= (array_length t0) - 1`)
  (sorted_array t0 `0` `(array_length t0) - 1`) /\ (permut t0 t).
Proof.
Intuition.
Assert h:`i1=0` \/ `0<i1`. Omega. Intuition.
Unfold sorted_array; Intros; Omega.
Replace `(array_length t0)-1` with `(i1-1)+1`.
Apply right_extension; Try Omega. 
Assumption.
Apply H5; Omega.
Omega.
Save.


