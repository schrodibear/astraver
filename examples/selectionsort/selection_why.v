(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Omega.

(*Why*) Parameter n : Z.

Lemma selection_po_1 : 
  (t: (array n Z))
  (Pre13: `n >= 1`)
  (result: Z)
  (Post11: result = `0`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array n Z))
  (Pre12: Variant1 = `n - i0`)
  (Pre11: (`0 <= i0` /\ `i0 <= n - 1`) /\ (sorted_array t0 `0` `i0 - 1`) /\
          (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i0` ->
            ((l:Z) (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i0 < n - 1`)
  (result1: Z)
  (Post8: result1 = i0)
  (result2: Z)
  (Post7: result2 = `i0 + 1`)
  (Variant3: Z)
  (j0: Z)
  (min0: Z)
  (Pre6: Variant3 = `n - j0`)
  (Pre5: (`i0 + 1 <= j0` /\ `j0 <= n`) /\ (`i0 <= min0` /\ `min0 < n`) /\
         ((k:Z)
          (`i0 <= k` /\ `k < j0` -> `(access t0 min0) <= (access t0 k)`)))
  (Test5: `j0 < n`)
  `0 <= min0` /\ `min0 < n`.
Proof.
Auto with *.
Save.

Lemma selection_po_2 : 
  (t: (array n Z))
  (Pre13: `n >= 1`)
  (result: Z)
  (Post11: result = `0`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array n Z))
  (Pre12: Variant1 = `n - i0`)
  (Pre11: (`0 <= i0` /\ `i0 <= n - 1`) /\ (sorted_array t0 `0` `i0 - 1`) /\
          (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i0` ->
            ((l:Z) (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i0 < n - 1`)
  (result1: Z)
  (Post8: result1 = i0)
  (result2: Z)
  (Post7: result2 = `i0 + 1`)
  (Variant3: Z)
  (j0: Z)
  (min0: Z)
  (Pre6: Variant3 = `n - j0`)
  (Pre5: (`i0 + 1 <= j0` /\ `j0 <= n`) /\ (`i0 <= min0` /\ `min0 < n`) /\
         ((k:Z)
          (`i0 <= k` /\ `k < j0` -> `(access t0 min0) <= (access t0 k)`)))
  (Test5: `j0 < n`)
  (Pre3: `0 <= min0` /\ `min0 < n`)
  `0 <= j0` /\ `j0 < n`.
Proof.
Intuition.
Save.

Lemma selection_po_3 : 
  (t: (array n Z))
  (Pre13: `n >= 1`)
  (result: Z)
  (Post11: result = `0`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array n Z))
  (Pre12: Variant1 = `n - i0`)
  (Pre11: (`0 <= i0` /\ `i0 <= n - 1`) /\ (sorted_array t0 `0` `i0 - 1`) /\
          (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i0` ->
            ((l:Z) (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i0 < n - 1`)
  (result1: Z)
  (Post8: result1 = i0)
  (result2: Z)
  (Post7: result2 = `i0 + 1`)
  (Variant3: Z)
  (j0: Z)
  (min0: Z)
  (Pre6: Variant3 = `n - j0`)
  (Pre5: (`i0 + 1 <= j0` /\ `j0 <= n`) /\ (`i0 <= min0` /\ `min0 < n`) /\
         ((k:Z)
          (`i0 <= k` /\ `k < j0` -> `(access t0 min0) <= (access t0 k)`)))
  (Test5: `j0 < n`)
  (Test4: `(access t0 j0) < (access t0 min0)`)
  (min1: Z)
  (Post1: min1 = j0)
  ((j:Z)
   (j = `j0 + 1` -> ((`i0 + 1 <= j` /\ `j <= n`) /\ (`i0 <= min1` /\
    `min1 < n`) /\
    ((k:Z) (`i0 <= k` /\ `k < j` -> `(access t0 min1) <= (access t0 k)`))) /\
    (Zwf `0` `n - j` `n - j0`))).
Proof.
Intuition.
Assert h: `k<j0` \/ `k=j0`. Omega. Intuition.
Apply Zle_trans with (access t0 min0).
Subst min1; Omega.
Apply H8; Omega.
Subst min1 k; Omega.
Unfold Zwf; Omega.
Save.

Lemma selection_po_4 : 
  (t: (array n Z))
  (Pre13: `n >= 1`)
  (result: Z)
  (Post11: result = `0`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array n Z))
  (Pre12: Variant1 = `n - i0`)
  (Pre11: (`0 <= i0` /\ `i0 <= n - 1`) /\ (sorted_array t0 `0` `i0 - 1`) /\
          (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i0` ->
            ((l:Z) (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i0 < n - 1`)
  (result1: Z)
  (Post8: result1 = i0)
  (result2: Z)
  (Post7: result2 = `i0 + 1`)
  (Variant3: Z)
  (j0: Z)
  (min0: Z)
  (Pre6: Variant3 = `n - j0`)
  (Pre5: (`i0 + 1 <= j0` /\ `j0 <= n`) /\ (`i0 <= min0` /\ `min0 < n`) /\
         ((k:Z)
          (`i0 <= k` /\ `k < j0` -> `(access t0 min0) <= (access t0 k)`)))
  (Test5: `j0 < n`)
  (Test3: `(access t0 j0) >= (access t0 min0)`)
  ((j:Z)
   (j = `j0 + 1` -> ((`i0 + 1 <= j` /\ `j <= n`) /\ (`i0 <= min0` /\
    `min0 < n`) /\
    ((k:Z) (`i0 <= k` /\ `k < j` -> `(access t0 min0) <= (access t0 k)`))) /\
    (Zwf `0` `n - j` `n - j0`))).
Proof.
Intuition.
Assert h: `k<j0` \/ `k=j0`. Omega. Intuition.
Subst k; Omega.
Unfold Zwf; Omega.
Save.

Lemma selection_po_5 : 
  (t: (array n Z))
  (Pre13: `n >= 1`)
  (result: Z)
  (Post11: result = `0`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array n Z))
  (Pre12: Variant1 = `n - i0`)
  (Pre11: (`0 <= i0` /\ `i0 <= n - 1`) /\ (sorted_array t0 `0` `i0 - 1`) /\
          (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i0` ->
            ((l:Z) (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i0 < n - 1`)
  (result1: Z)
  (Post8: result1 = i0)
  (result2: Z)
  (Post7: result2 = `i0 + 1`)
  (Variant3: Z)
  (j0: Z)
  (min0: Z)
  (Pre6: Variant3 = `n - j0`)
  (Pre5: (`i0 + 1 <= j0` /\ `j0 <= n`) /\ (`i0 <= min0` /\ `min0 < n`) /\
         ((k:Z)
          (`i0 <= k` /\ `k < j0` -> `(access t0 min0) <= (access t0 k)`)))
  (Test5: `j0 < n`)
  (min1: Z)
  (Post21: ((j:Z)
            (j = `j0 + 1` -> ((`i0 + 1 <= j` /\ `j <= n`) /\ (`i0 <= min1` /\
             `min1 < n`) /\
             ((k:Z)
              (`i0 <= k` /\ `k < j` -> `(access t0 min1) <= (access t0 k)`))) /\
             (Zwf `0` `n - j` `n - j0`))))
  (j1: Z)
  (Post2: j1 = `j0 + 1`)
  ((`i0 + 1 <= j1` /\ `j1 <= n`) /\ (`i0 <= min1` /\ `min1 < n`) /\
  ((k:Z) (`i0 <= k` /\ `k < j1` -> `(access t0 min1) <= (access t0 k)`))) /\
  (Zwf `0` `n - j1` `n - j0`).
Proof.
Intuition.
Save.

Lemma selection_po_6 : 
  (t: (array n Z))
  (Pre13: `n >= 1`)
  (result: Z)
  (Post11: result = `0`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array n Z))
  (Pre12: Variant1 = `n - i0`)
  (Pre11: (`0 <= i0` /\ `i0 <= n - 1`) /\ (sorted_array t0 `0` `i0 - 1`) /\
          (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i0` ->
            ((l:Z) (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i0 < n - 1`)
  (result1: Z)
  (Post8: result1 = i0)
  (result2: Z)
  (Post7: result2 = `i0 + 1`)
  (`i0 + 1 <= result2` /\ `result2 <= n`) /\ (`i0 <= result1` /\
  `result1 < n`) /\
  ((k:Z)
   (`i0 <= k` /\ `k < result2` -> `(access t0 result1) <= (access t0 k)`)).
Proof.
Intuition.
Assert h:`k=i0`. Omega.
Subst result1 k; Omega.
Save.

Lemma selection_po_7 : 
  (t: (array n Z))
  (Pre13: `n >= 1`)
  (result: Z)
  (Post11: result = `0`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array n Z))
  (Pre12: Variant1 = `n - i0`)
  (Pre11: (`0 <= i0` /\ `i0 <= n - 1`) /\ (sorted_array t0 `0` `i0 - 1`) /\
          (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i0` ->
            ((l:Z) (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i0 < n - 1`)
  (result1: Z)
  (Post8: result1 = i0)
  (result2: Z)
  (Post7: result2 = `i0 + 1`)
  (j0: Z)
  (min0: Z)
  (Post3: ((`i0 + 1 <= j0` /\ `j0 <= n`) /\ (`i0 <= min0` /\ `min0 < n`) /\
          ((k:Z)
           (`i0 <= k` /\ `k < j0` -> `(access t0 min0) <= (access t0 k)`))) /\
          `j0 >= n`)
  `0 <= min0` /\ `min0 < n`.
Proof.
Intuition.
Save.

Lemma selection_po_8 : 
  (t: (array n Z))
  (Pre13: `n >= 1`)
  (result: Z)
  (Post11: result = `0`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array n Z))
  (Pre12: Variant1 = `n - i0`)
  (Pre11: (`0 <= i0` /\ `i0 <= n - 1`) /\ (sorted_array t0 `0` `i0 - 1`) /\
          (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i0` ->
            ((l:Z) (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i0 < n - 1`)
  (result1: Z)
  (Post8: result1 = i0)
  (result2: Z)
  (Post7: result2 = `i0 + 1`)
  (j0: Z)
  (min0: Z)
  (Post3: ((`i0 + 1 <= j0` /\ `j0 <= n`) /\ (`i0 <= min0` /\ `min0 < n`) /\
          ((k:Z)
           (`i0 <= k` /\ `k < j0` -> `(access t0 min0) <= (access t0 k)`))) /\
          `j0 >= n`)
  (Pre7: `0 <= min0` /\ `min0 < n`)
  (w: Z)
  (Post6: w = (access t0 min0))
  `0 <= i0` /\ `i0 < n`.
Proof.
Intuition.
Save.

Lemma selection_po_9 : 
  (t: (array n Z))
  (Pre13: `n >= 1`)
  (result: Z)
  (Post11: result = `0`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array n Z))
  (Pre12: Variant1 = `n - i0`)
  (Pre11: (`0 <= i0` /\ `i0 <= n - 1`) /\ (sorted_array t0 `0` `i0 - 1`) /\
          (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i0` ->
            ((l:Z) (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i0 < n - 1`)
  (result1: Z)
  (Post8: result1 = i0)
  (result2: Z)
  (Post7: result2 = `i0 + 1`)
  (j0: Z)
  (min0: Z)
  (Post3: ((`i0 + 1 <= j0` /\ `j0 <= n`) /\ (`i0 <= min0` /\ `min0 < n`) /\
          ((k:Z)
           (`i0 <= k` /\ `k < j0` -> `(access t0 min0) <= (access t0 k)`))) /\
          `j0 >= n`)
  (Pre7: `0 <= min0` /\ `min0 < n`)
  (w: Z)
  (Post6: w = (access t0 min0))
  (Pre8: `0 <= i0` /\ `i0 < n`)
  (t1: (array n Z))
  (Post4: t1 = (store t0 min0 (access t0 i0)))
  (t2: (array n Z))
  (Post5: t2 = (store t1 i0 w))
  ((i:Z)
   (i = `i0 + 1` -> ((`0 <= i` /\ `i <= n - 1`) /\
    (sorted_array t2 `0` `i - 1`) /\ (permut t2 t) /\
    ((k:Z)
     (`0 <= k` /\ `k < i` ->
      ((l:Z) (`i <= l` /\ `l < n` -> `(access t2 k) <= (access t2 l)`))))) /\
    (Zwf `0` `n - i` `n - i0`))).
Proof.
Intuition.
Assert h: `i0=0` \/ `0<i0`. Omega. Intuition.
Replace `i-1` with `0`.
Unfold sorted_array; Intros; Omega.
Omega.
Replace `i-1` with `(i0-1)+1`.
Apply right_extension.
Omega.
Omega.
Apply sorted_array_id with t0.
Assumption.
Unfold array_id; Intros.
Subst t2; Rewrite store_def_2; Try Omega.
Subst t1; Rewrite store_def_2; Try Omega.
Replace `i0-1+1` with i0.
Subst t2; Rewrite store_def_2; Try Omega.
Rewrite store_def_1; Try Omega.
Subst t1; Rewrite store_def_2; Try Omega.
Subst w.
Apply H4; Omega.
Omega.
Omega.
Apply permut_trans with t0.
Subst t2; Subst t1; Subst w.
Apply exchange_is_permut with min0 i0; Auto with *.
Assumption.
Assert h:`k=i0` \/ `k<i0`. Omega. Intuition.
Subst k.
Subst t2.
Rewrite store_def_1; Try Omega.
Rewrite store_def_2; Try Omega.
Subst t1.
Assert h:`l=min0` \/ `min0<>l`. Omega. Intuition.
Subst l; Rewrite store_def_1; Try Omega.
Subst w; Apply H11; Omega.
Rewrite store_def_2; Try Omega.
Subst w; Apply H11; Omega.
Subst t2. Rewrite store_def_2; Try Omega.
Rewrite store_def_2; Try Omega.
Subst t1. 
Assert h:`l=min0` \/ `min0<>l`. Omega. Intuition.
Subst l; Rewrite store_def_1; Try Omega.
Rewrite store_def_2; Try Omega.
Apply H4; Omega.
Rewrite store_def_2; Try Omega.
Rewrite store_def_2; Try Omega.
Apply H4; Omega.
Unfold Zwf; Omega.
Save.

Lemma selection_po_10 : 
  (t: (array n Z))
  (Pre13: `n >= 1`)
  (result: Z)
  (Post11: result = `0`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array n Z))
  (Pre12: Variant1 = `n - i0`)
  (Pre11: (`0 <= i0` /\ `i0 <= n - 1`) /\ (sorted_array t0 `0` `i0 - 1`) /\
          (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i0` ->
            ((l:Z) (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`)))))
  (Test6: `i0 < n - 1`)
  (t1: (array n Z))
  (Post17: ((i:Z)
            (i = `i0 + 1` -> ((`0 <= i` /\ `i <= n - 1`) /\
             (sorted_array t1 `0` `i - 1`) /\ (permut t1 t) /\
             ((k:Z)
              (`0 <= k` /\ `k < i` ->
               ((l:Z)
                (`i <= l` /\ `l < n` -> `(access t1 k) <= (access t1 l)`))))) /\
             (Zwf `0` `n - i` `n - i0`))))
  (i1: Z)
  (Post9: i1 = `i0 + 1`)
  ((`0 <= i1` /\ `i1 <= n - 1`) /\ (sorted_array t1 `0` `i1 - 1`) /\
  (permut t1 t) /\
  ((k:Z)
   (`0 <= k` /\ `k < i1` ->
    ((l:Z) (`i1 <= l` /\ `l < n` -> `(access t1 k) <= (access t1 l)`))))) /\
  (Zwf `0` `n - i1` `n - i0`).
Proof.
Intuition.
Save.

Lemma selection_po_11 : 
  (t: (array n Z))
  (Pre13: `n >= 1`)
  (result: Z)
  (Post11: result = `0`)
  (`0 <= result` /\ `result <= n - 1`) /\
  (sorted_array t `0` `result - 1`) /\ (permut t t) /\
  ((k:Z)
   (`0 <= k` /\ `k < result` ->
    ((l:Z) (`result <= l` /\ `l < n` -> `(access t k) <= (access t l)`)))).
Proof.
Intuition.
Unfold sorted_array; Intros; Omega.
Save.

Lemma selection_po_12 : 
  (t: (array n Z))
  (Pre13: `n >= 1`)
  (result: Z)
  (Post11: result = `0`)
  (i0: Z)
  (t0: (array n Z))
  (Post10: ((`0 <= i0` /\ `i0 <= n - 1`) /\ (sorted_array t0 `0` `i0 - 1`) /\
           (permut t0 t) /\
           ((k:Z)
            (`0 <= k` /\ `k < i0` ->
             ((l:Z)
              (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`))))) /\
           `i0 >= n - 1`)
  (sorted_array t0 `0` `n - 1`) /\ (permut t0 t).
Proof.
Intuition.
Assert h:`i0=0` \/ `0<i0`. Omega. Intuition.
Unfold sorted_array; Intros; Omega.
Replace `n-1` with `(i0-1)+1`.
Apply right_extension; Try Omega. 
Assumption.
Apply H5; Omega.
Omega.
Save.

Definition selection := (* validation *)
  [t: (array n Z); Pre13: `n >= 1`]
    let (t0, result, Post15) =
      let (result, Post11) = (exist_1 [result: Z]result = `0` `0`
        (refl_equal ? `0`)) in
      let (i0, t0, result0, Post10) =
        (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
          [Variant1: Z](i0: Z)(t0: (array n Z))(_: Variant1 = `n - i0`)
          (_0: (`0 <= i0` /\ `i0 <= n - 1`) /\
          (sorted_array t0 `0` `i0 - 1`) /\ (permut t0 t) /\
          ((k:Z)
           (`0 <= k` /\ `k < i0` ->
            ((l:Z) (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`)))))
          (sig_3 Z (array n Z) unit [i1: Z][t1: (array n Z)][result0: unit]
           (((`0 <= i1` /\ `i1 <= n - 1`) /\
           (sorted_array t1 `0` `i1 - 1`) /\ (permut t1 t) /\
           ((k:Z)
            (`0 <= k` /\ `k < i1` ->
             ((l:Z)
              (`i1 <= l` /\ `l < n` -> `(access t1 k) <= (access t1 l)`))))) /\
           `i1 >= n - 1`))
          [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
           (i0: Z)(t0: (array n Z))(_: Variant2 = `n - i0`)(_0: (`0 <= i0` /\
           `i0 <= n - 1`) /\ (sorted_array t0 `0` `i0 - 1`) /\
           (permut t0 t) /\
           ((k:Z)
            (`0 <= k` /\ `k < i0` ->
             ((l:Z)
              (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`)))))
           (sig_3 Z (array n Z) unit [i1: Z][t1: (array n Z)][result0: unit]
            (((`0 <= i1` /\ `i1 <= n - 1`) /\
            (sorted_array t1 `0` `i1 - 1`) /\ (permut t1 t) /\
            ((k:Z)
             (`0 <= k` /\ `k < i1` ->
              ((l:Z)
               (`i1 <= l` /\ `l < n` -> `(access t1 k) <= (access t1 l)`))))) /\
            `i1 >= n - 1`));
           i0: Z; t0: (array n Z); Pre12: Variant1 = `n - i0`;
           Pre11: (`0 <= i0` /\ `i0 <= n - 1`) /\
           (sorted_array t0 `0` `i0 - 1`) /\ (permut t0 t) /\
           ((k:Z)
            (`0 <= k` /\ `k < i0` ->
             ((l:Z)
              (`i0 <= l` /\ `l < n` -> `(access t0 k) <= (access t0 l)`))))]
            let (result0, Bool3) =
              let (result2, Post16) = (Z_lt_ge_bool i0 `n - 1`) in
              (exist_1 [result3: bool]
              (if result3 then `i0 < n - 1` else `i0 >= n - 1`) result2
              Post16) in
            (Cases (btest
                    [result0:bool](if result0 then `i0 < n - 1`
                                   else `i0 >= n - 1`)
                    result0 Bool3) of
            | (left Test6) =>
                let (i1, t1, result1, Post10) =
                  let (i1, t1, result1, Post12) =
                    let (t1, result1, Post17) =
                      let (result1, Post8) = (exist_1 [result1: Z]
                        result1 = i0 i0 (refl_equal ? i0)) in
                      let (min0, t1, result2, Post18) =
                        let (result2, Post7) = (exist_1 [result2: Z]
                          result2 = `i0 + 1` `i0 + 1`
                          (refl_equal ? `i0 + 1`)) in
                        let (j0, min0, t1, result3, Post19) =
                          let (j0, min0, result3, Post3) =
                            (well_founded_induction Z (Zwf ZERO)
                              (Zwf_well_founded `0`) [Variant3: Z](j0: Z)
                              (min0: Z)(_: Variant3 = `n - j0`)
                              (_0: (`i0 + 1 <= j0` /\ `j0 <= n`) /\
                              (`i0 <= min0` /\ `min0 < n`) /\
                              ((k:Z)
                               (`i0 <= k` /\ `k < j0` ->
                                `(access t0 min0) <= (access t0 k)`)))
                              (sig_3 Z Z unit [j1: Z][min1: Z][result3: unit]
                               (((`i0 + 1 <= j1` /\ `j1 <= n`) /\
                               (`i0 <= min1` /\ `min1 < n`) /\
                               ((k:Z)
                                (`i0 <= k` /\ `k < j1` ->
                                 `(access t0 min1) <= (access t0 k)`))) /\
                               `j1 >= n`))
                              [Variant3: Z; wf2: (Variant4: Z)
                               (Pre2: (Zwf `0` Variant4 Variant3))(j0: Z)
                               (min0: Z)(_: Variant4 = `n - j0`)
                               (_0: (`i0 + 1 <= j0` /\ `j0 <= n`) /\
                               (`i0 <= min0` /\ `min0 < n`) /\
                               ((k:Z)
                                (`i0 <= k` /\ `k < j0` ->
                                 `(access t0 min0) <= (access t0 k)`)))
                               (sig_3 Z Z unit [j1: Z][min1: Z]
                                [result3: unit](((`i0 + 1 <= j1` /\
                                `j1 <= n`) /\ (`i0 <= min1` /\ `min1 < n`) /\
                                ((k:Z)
                                 (`i0 <= k` /\ `k < j1` ->
                                  `(access t0 min1) <= (access t0 k)`))) /\
                                `j1 >= n`));
                               j0: Z; min0: Z; Pre6: Variant3 = `n - j0`;
                               Pre5: (`i0 + 1 <= j0` /\ `j0 <= n`) /\
                               (`i0 <= min0` /\ `min0 < n`) /\
                               ((k:Z)
                                (`i0 <= k` /\ `k < j0` ->
                                 `(access t0 min0) <= (access t0 k)`))]
                                let (result3, Bool2) =
                                  let (result5, Post20) =
                                    (Z_lt_ge_bool j0 n) in
                                  (exist_1 [result6: bool]
                                  (if result6 then `j0 < n` else `j0 >= n`) 
                                  result5 Post20) in
                                (Cases (btest
                                        [result3:bool](if result3
                                                       then `j0 < n`
                                                       else `j0 >= n`)
                                        result3 Bool2) of
                                | (left Test5) =>
                                    let (j1, min1, result4, Post3) =
                                      let (j1, min1, result4, Post13) =
                                        let (min1, result4, Post21) =
                                          let (result4, Bool1) =
                                            let Pre3 =
                                              (selection_po_1 t Pre13 result
                                              Post11 Variant1 i0 t0 Pre12
                                              Pre11 Test6 result1 Post8
                                              result2 Post7 Variant3 j0 min0
                                              Pre6 Pre5 Test5) in
                                            let result5 =
                                              let Pre4 =
                                                (selection_po_2 t Pre13
                                                result Post11 Variant1 i0 t0
                                                Pre12 Pre11 Test6 result1
                                                Post8 result2 Post7 Variant3
                                                j0 min0 Pre6 Pre5 Test5 Pre3) in
                                              (Z_lt_ge_bool (access t0 j0)) in
                                            let (result6, Post22) =
                                              (result5 (access t0 min0)) in
                                            (exist_1 [result7: bool]
                                            (if result7
                                             then `(access t0 j0) <
                                                   (access t0 min0)`
                                             else `(access t0 j0) >=
                                                   (access t0 min0)`) 
                                            result6 Post22) in
                                          (Cases (btest
                                                  [result4:bool](if result4
                                                                 then `
                                                                 (access t0
                                                                  j0) <
                                                                 (access t0
                                                                  min0)`
                                                                 else `
                                                                 (access t0
                                                                  j0) >=
                                                                 (access t0
                                                                  min0)`)
                                                  result4 Bool1) of
                                          | (left Test4) =>
                                              let (min1, result5, Post1) =
                                                let (result5, Post1) =
                                                  (exist_1 [result5: Z]
                                                  result5 = j0 j0
                                                  (refl_equal ? j0)) in
                                                (exist_2 [min2: Z]
                                                [result6: unit]
                                                min2 = j0 result5 tt Post1) in
                                              (exist_2 [min2: Z]
                                              [result6: unit]
                                              ((j:Z)
                                               (j = `j0 + 1` ->
                                                ((`i0 + 1 <= j` /\
                                                `j <= n`) /\ (`i0 <= min2` /\
                                                `min2 < n`) /\
                                                ((k:Z)
                                                 (`i0 <= k` /\ `k < j` ->
                                                  `(access t0 min2) <=
                                                   (access t0 k)`))) /\
                                                (Zwf `0` `n - j` `n - j0`))) 
                                              min1 result5
                                              (selection_po_3 t Pre13 result
                                              Post11 Variant1 i0 t0 Pre12
                                              Pre11 Test6 result1 Post8
                                              result2 Post7 Variant3 j0 min0
                                              Pre6 Pre5 Test5 Test4 min1
                                              Post1))
                                          | (right Test3) =>
                                              let (result5, Post23) =
                                                (exist_1 [result5: unit]
                                                ((j:Z)
                                                 (j = `j0 + 1` ->
                                                  ((`i0 + 1 <= j` /\
                                                  `j <= n`) /\
                                                  (`i0 <= min0` /\
                                                  `min0 < n`) /\
                                                  ((k:Z)
                                                   (`i0 <= k` /\ `k < j` ->
                                                    `(access t0 min0) <=
                                                     (access t0 k)`))) /\
                                                  (Zwf `0` `n - j` `n - j0`))) 
                                                tt
                                                (selection_po_4 t Pre13
                                                result Post11 Variant1 i0 t0
                                                Pre12 Pre11 Test6 result1
                                                Post8 result2 Post7 Variant3
                                                j0 min0 Pre6 Pre5 Test5
                                                Test3)) in
                                              (exist_2 [min1: Z]
                                              [result6: unit]
                                              ((j:Z)
                                               (j = `j0 + 1` ->
                                                ((`i0 + 1 <= j` /\
                                                `j <= n`) /\ (`i0 <= min1` /\
                                                `min1 < n`) /\
                                                ((k:Z)
                                                 (`i0 <= k` /\ `k < j` ->
                                                  `(access t0 min1) <=
                                                   (access t0 k)`))) /\
                                                (Zwf `0` `n - j` `n - j0`))) 
                                              min0 result5 Post23) end) in
                                        let (j1, result5, Post2) =
                                          let (result5, Post2) =
                                            (exist_1 [result5: Z]
                                            result5 = `j0 + 1` `j0 + 1`
                                            (refl_equal ? `j0 + 1`)) in
                                          (exist_2 [j2: Z][result6: unit]
                                          j2 = `j0 + 1` result5 tt Post2) in
                                        (exist_3 [j2: Z][min2: Z]
                                        [result6: unit]((`i0 + 1 <= j2` /\
                                        `j2 <= n`) /\ (`i0 <= min2` /\
                                        `min2 < n`) /\
                                        ((k:Z)
                                         (`i0 <= k` /\ `k < j2` ->
                                          `(access t0 min2) <= (access t0 k)`))) /\
                                        (Zwf `0` `n - j2` `n - j0`) j1 
                                        min1 result5
                                        (selection_po_5 t Pre13 result Post11
                                        Variant1 i0 t0 Pre12 Pre11 Test6
                                        result1 Post8 result2 Post7 Variant3
                                        j0 min0 Pre6 Pre5 Test5 min1 Post21
                                        j1 Post2)) in
                                      ((wf2 `n - j1`)
                                        (loop_variant_1 Pre6 Post13) 
                                        j1 min1 (refl_equal ? `n - j1`)
                                        (proj1 ? ? Post13)) in
                                    (exist_3 [j2: Z][min2: Z][result5: unit]
                                    ((`i0 + 1 <= j2` /\ `j2 <= n`) /\
                                    (`i0 <= min2` /\ `min2 < n`) /\
                                    ((k:Z)
                                     (`i0 <= k` /\ `k < j2` ->
                                      `(access t0 min2) <= (access t0 k)`))) /\
                                    `j2 >= n` j1 min1 result4 Post3)
                                | (right Test2) =>
                                    let (j1, min1, result4, Post3) =
                                      (exist_3 [j1: Z][min1: Z]
                                      [result4: unit]((`i0 + 1 <= j1` /\
                                      `j1 <= n`) /\ (`i0 <= min1` /\
                                      `min1 < n`) /\
                                      ((k:Z)
                                       (`i0 <= k` /\ `k < j1` ->
                                        `(access t0 min1) <= (access t0 k)`))) /\
                                      `j1 >= n` j0 min0 tt
                                      (conj ? ? Pre5 Test2)) in
                                    (exist_3 [j2: Z][min2: Z][result5: unit]
                                    ((`i0 + 1 <= j2` /\ `j2 <= n`) /\
                                    (`i0 <= min2` /\ `min2 < n`) /\
                                    ((k:Z)
                                     (`i0 <= k` /\ `k < j2` ->
                                      `(access t0 min2) <= (access t0 k)`))) /\
                                    `j2 >= n` j1 min1 result4 Post3) end)
                              `n - result2` result2 result1
                              (refl_equal ? `n - result2`)
                              (selection_po_6 t Pre13 result Post11 Variant1
                              i0 t0 Pre12 Pre11 Test6 result1 Post8 result2
                              Post7)) in
                          let (t1, result4, Post24) =
                            let Pre7 =
                              (selection_po_7 t Pre13 result Post11 Variant1
                              i0 t0 Pre12 Pre11 Test6 result1 Post8 result2
                              Post7 j0 min0 Post3) in
                            let (w, Post6) = (exist_1 [result4: Z]
                              result4 = (access t0 min0) (access t0 min0)
                              (refl_equal ? (access t0 min0))) in
                            let (t1, result4, Post25) =
                              let Pre8 =
                                (selection_po_8 t Pre13 result Post11
                                Variant1 i0 t0 Pre12 Pre11 Test6 result1
                                Post8 result2 Post7 j0 min0 Post3 Pre7 w
                                Post6) in
                              let (t1, result4, Post4) =
                                let (result4, Post4) = (exist_1 [result4: Z]
                                  (store t0 min0 result4) = (store t0 min0
                                                             (access t0 i0)) 
                                  (access t0 i0)
                                  (refl_equal ? (store t0 min0 (access t0 i0)))) in
                                let Pre9 = Pre7 in
                                (exist_2 [t2: (array n Z)][result6: unit]
                                t2 = (store t0 min0 (access t0 i0)) (
                                                                    store t0
                                                                    min0
                                                                    result4)
                                tt Post4) in
                              let (t2, result5, Post5) =
                                let (result5, Post5) = (exist_1 [result5: Z]
                                  (store t1 i0 result5) = (store t1 i0 w) 
                                  w (refl_equal ? (store t1 i0 w))) in
                                let Pre10 = Pre8 in
                                (exist_2 [t3: (array n Z)][result7: unit]
                                t3 = (store t1 i0 w) (store t1 i0 result5) 
                                tt Post5) in
                              (exist_2 [t3: (array n Z)][result6: unit]
                              ((i:Z)
                               (i = `i0 + 1` -> ((`0 <= i` /\
                                `i <= n - 1`) /\
                                (sorted_array t3 `0` `i - 1`) /\
                                (permut t3 t) /\
                                ((k:Z)
                                 (`0 <= k` /\ `k < i` ->
                                  ((l:Z)
                                   (`i <= l` /\ `l < n` ->
                                    `(access t3 k) <= (access t3 l)`))))) /\
                                (Zwf `0` `n - i` `n - i0`))) t2
                              result5
                              (selection_po_9 t Pre13 result Post11 Variant1
                              i0 t0 Pre12 Pre11 Test6 result1 Post8 result2
                              Post7 j0 min0 Post3 Pre7 w Post6 Pre8 t1 Post4
                              t2 Post5)) in
                            (exist_2 [t2: (array n Z)][result5: unit]
                            ((i:Z)
                             (i = `i0 + 1` -> ((`0 <= i` /\ `i <= n - 1`) /\
                              (sorted_array t2 `0` `i - 1`) /\
                              (permut t2 t) /\
                              ((k:Z)
                               (`0 <= k` /\ `k < i` ->
                                ((l:Z)
                                 (`i <= l` /\ `l < n` ->
                                  `(access t2 k) <= (access t2 l)`))))) /\
                              (Zwf `0` `n - i` `n - i0`))) t1
                            result4 Post25) in
                          (exist_4 [j1: Z][min1: Z][t2: (array n Z)]
                          [result5: unit]
                          ((i:Z)
                           (i = `i0 + 1` -> ((`0 <= i` /\ `i <= n - 1`) /\
                            (sorted_array t2 `0` `i - 1`) /\ (permut t2 t) /\
                            ((k:Z)
                             (`0 <= k` /\ `k < i` ->
                              ((l:Z)
                               (`i <= l` /\ `l < n` ->
                                `(access t2 k) <= (access t2 l)`))))) /\
                            (Zwf `0` `n - i` `n - i0`))) j0
                          min0 t1 result4 Post24) in
                        (exist_3 [min1: Z][t2: (array n Z)][result4: unit]
                        ((i:Z)
                         (i = `i0 + 1` -> ((`0 <= i` /\ `i <= n - 1`) /\
                          (sorted_array t2 `0` `i - 1`) /\ (permut t2 t) /\
                          ((k:Z)
                           (`0 <= k` /\ `k < i` ->
                            ((l:Z)
                             (`i <= l` /\ `l < n` ->
                              `(access t2 k) <= (access t2 l)`))))) /\
                          (Zwf `0` `n - i` `n - i0`))) min0
                        t1 result3 Post19) in
                      (exist_2 [t2: (array n Z)][result3: unit]
                      ((i:Z)
                       (i = `i0 + 1` -> ((`0 <= i` /\ `i <= n - 1`) /\
                        (sorted_array t2 `0` `i - 1`) /\ (permut t2 t) /\
                        ((k:Z)
                         (`0 <= k` /\ `k < i` ->
                          ((l:Z)
                           (`i <= l` /\ `l < n` ->
                            `(access t2 k) <= (access t2 l)`))))) /\
                        (Zwf `0` `n - i` `n - i0`))) t1
                      result2 Post18) in
                    let (i1, result2, Post9) =
                      let (result2, Post9) = (exist_1 [result2: Z]
                        result2 = `i0 + 1` `i0 + 1`
                        (refl_equal ? `i0 + 1`)) in
                      (exist_2 [i2: Z][result3: unit]i2 = `i0 + 1` result2 
                      tt Post9) in
                    (exist_3 [i2: Z][t2: (array n Z)][result3: unit]
                    ((`0 <= i2` /\ `i2 <= n - 1`) /\
                    (sorted_array t2 `0` `i2 - 1`) /\ (permut t2 t) /\
                    ((k:Z)
                     (`0 <= k` /\ `k < i2` ->
                      ((l:Z)
                       (`i2 <= l` /\ `l < n` ->
                        `(access t2 k) <= (access t2 l)`))))) /\
                    (Zwf `0` `n - i2` `n - i0`) i1 t1 result2
                    (selection_po_10 t Pre13 result Post11 Variant1 i0 t0
                    Pre12 Pre11 Test6 t1 Post17 i1 Post9)) in
                  ((wf1 `n - i1`) (loop_variant_1 Pre12 Post12) i1 t1
                    (refl_equal ? `n - i1`) (proj1 ? ? Post12)) in
                (exist_3 [i2: Z][t2: (array n Z)][result2: unit]
                ((`0 <= i2` /\ `i2 <= n - 1`) /\
                (sorted_array t2 `0` `i2 - 1`) /\ (permut t2 t) /\
                ((k:Z)
                 (`0 <= k` /\ `k < i2` ->
                  ((l:Z)
                   (`i2 <= l` /\ `l < n` -> `(access t2 k) <= (access t2 l)`))))) /\
                `i2 >= n - 1` i1 t1 result1 Post10)
            | (right Test1) =>
                let (i1, t1, result1, Post10) = (exist_3 [i1: Z]
                  [t1: (array n Z)][result1: unit]((`0 <= i1` /\
                  `i1 <= n - 1`) /\ (sorted_array t1 `0` `i1 - 1`) /\
                  (permut t1 t) /\
                  ((k:Z)
                   (`0 <= k` /\ `k < i1` ->
                    ((l:Z)
                     (`i1 <= l` /\ `l < n` ->
                      `(access t1 k) <= (access t1 l)`))))) /\
                  `i1 >= n - 1` i0 t0 tt (conj ? ? Pre11 Test1)) in
                (exist_3 [i2: Z][t2: (array n Z)][result2: unit]
                ((`0 <= i2` /\ `i2 <= n - 1`) /\
                (sorted_array t2 `0` `i2 - 1`) /\ (permut t2 t) /\
                ((k:Z)
                 (`0 <= k` /\ `k < i2` ->
                  ((l:Z)
                   (`i2 <= l` /\ `l < n` -> `(access t2 k) <= (access t2 l)`))))) /\
                `i2 >= n - 1` i1 t1 result1 Post10) end) `n - result` 
          result t (refl_equal ? `n - result`)
          (selection_po_11 t Pre13 result Post11)) in
      (exist_2 [t1: (array n Z)][result1: unit]
      (sorted_array t1 `0` `n - 1`) /\ (permut t1 t) t0 result0
      (selection_po_12 t Pre13 result Post11 i0 t0 Post10)) in
    (exist_2 [t1: (array n Z)][result0: unit](sorted_array t1 `0` `n - 1`) /\
    (permut t1 t) t0 result Post15).

