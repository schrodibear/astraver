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

Lemma heapsort_po_1 : 
  (N: Z)
  (t: (array N Z))
  (Pre16: `1 <= N`)
  (result: Z)
  (Post3: result = (Zdiv2 `N - 2`))
  (Variant1: Z)
  (k0: Z)
  (t0: (array N Z))
  (Pre6: Variant1 = `k0 + 1`)
  (Pre5: (`(-1) <= k0` /\ `k0 <= N - 1`) /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= N - 1` -> (heap t0 `N - 1` i))) /\
         (permut t0 t))
  (Test2: `k0 >= 0`)
  (`0 <= k0` /\ `k0 <= N - 1`) /\ `N - 1 < N` /\
  ((i:Z) (`k0 + 1 <= i` /\ `i <= N - 1` -> (heap t0 `N - 1` i))).
Proof.
Intuition.
Save.

Lemma heapsort_po_2 : 
  (N: Z)
  (t: (array N Z))
  (Pre16: `1 <= N`)
  (result: Z)
  (Post3: result = (Zdiv2 `N - 2`))
  (Variant1: Z)
  (k0: Z)
  (t0: (array N Z))
  (Pre6: Variant1 = `k0 + 1`)
  (Pre5: (`(-1) <= k0` /\ `k0 <= N - 1`) /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= N - 1` -> (heap t0 `N - 1` i))) /\
         (permut t0 t))
  (Test2: `k0 >= 0`)
  (Pre4: (`0 <= k0` /\ `k0 <= N - 1`) /\ `N - 1 < N` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= N - 1` -> (heap t0 `N - 1` i))))
  (t1: (array N Z))
  (Post11: (permut t1 t0) /\
           ((i:Z) (`k0 <= i` /\ `i <= N - 1` -> (heap t1 `N - 1` i))) /\
           ((i:Z)
            (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
             `N - 1 < i` /\ `i < N` -> `(access t1 i) = (access t0 i)`)) /\
           ((v:Z) ((inftree t0 `N - 1` v k0) -> (inftree t1 `N - 1` v k0))))
  (k1: Z)
  (Post1: k1 = `k0 - 1`)
  ((`(-1) <= k1` /\ `k1 <= N - 1`) /\
  ((i:Z) (`k1 + 1 <= i` /\ `i <= N - 1` -> (heap t1 `N - 1` i))) /\
  (permut t1 t)) /\ (Zwf `0` `k1 + 1` `k0 + 1`).
Proof.
Intuition.
Apply permut_trans with t':=t0; Assumption.
Unfold Zwf; Omega'.
Save.

Lemma heapsort_po_3 : 
  (N: Z)
  (t: (array N Z))
  (Pre16: `1 <= N`)
  (result: Z)
  (Post3: result = (Zdiv2 `N - 2`))
  (`(-1) <= result` /\ `result <= N - 1`) /\
  ((i:Z) (`result + 1 <= i` /\ `i <= N - 1` -> (heap t `N - 1` i))) /\
  (permut t t).
Proof.
Intros.
Generalize (lem_div2_0 N Pre16); Intuition Try Omega'.
Apply heap_leaf.
Generalize (lem_div2_1 N Pre16); Omega'.
Apply (lem_div2_2 N i); Trivial Orelse Omega'.
Auto with datatypes.
Save.

Lemma heapsort_po_4 : 
  (N: Z)
  (t: (array N Z))
  (Pre16: `1 <= N`)
  (result: Z)
  (Post3: result = (Zdiv2 `N - 2`))
  (k0: Z)
  (t0: (array N Z))
  (Post2: ((`(-1) <= k0` /\ `k0 <= N - 1`) /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= N - 1` -> (heap t0 `N - 1` i))) /\
          (permut t0 t)) /\ `k0 < 0`)
  (heap t0 `N - 1` `0`) /\ (permut t0 t).
Proof.
Intuition.
Save.

Lemma heapsort_po_5 : 
  (N: Z)
  (t: (array N Z))
  (Pre16: `1 <= N`)
  (t0: (array N Z))
  (Post9: (heap t0 `N - 1` `0`) /\ (permut t0 t))
  (result0: Z)
  (Post6: result0 = `N - 1`)
  (Variant3: Z)
  (k0: Z)
  (t1: (array N Z))
  (Pre15: Variant3 = k0)
  (Pre14: (`0 <= k0` /\ `k0 <= N - 1`) /\
          ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
          ((`k0 + 1 <= N - 1` -> `(access t1 0) <= (access t1 k0 + 1)`)) /\
          ((`k0 + 1 <= N - 1` -> (sorted_array t1 `k0 + 1` `N - 1`))) /\
          (permut t1 t))
  (Test4: `k0 >= 1`)
  (`0 <= 0` /\ `0 < N`) /\ `0 <= k0` /\ `k0 < N`.
Proof.
Intuition.
Save.

Lemma heapsort_po_6 : 
  (N: Z)
  (t: (array N Z))
  (Pre16: `1 <= N`)
  (t0: (array N Z))
  (Post9: (heap t0 `N - 1` `0`) /\ (permut t0 t))
  (result0: Z)
  (Post6: result0 = `N - 1`)
  (Variant3: Z)
  (k0: Z)
  (t1: (array N Z))
  (Pre15: Variant3 = k0)
  (Pre14: (`0 <= k0` /\ `k0 <= N - 1`) /\
          ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
          ((`k0 + 1 <= N - 1` -> `(access t1 0) <= (access t1 k0 + 1)`)) /\
          ((`k0 + 1 <= N - 1` -> (sorted_array t1 `k0 + 1` `N - 1`))) /\
          (permut t1 t))
  (Test4: `k0 >= 1`)
  (Pre13: (`0 <= 0` /\ `0 < N`) /\ `0 <= k0` /\ `k0 < N`)
  (t2: (array N Z))
  (Post15: (exchange t2 t1 `0` k0))
  (`0 <= 0` /\ `0 <= k0 - 1`) /\ `k0 - 1 < N` /\
  ((i:Z) (`0 + 1 <= i` /\ `i <= k0 - 1` -> (heap t2 `k0 - 1` i))).
Proof.
Intuition.
Apply heap_id with t:=t1.
Apply heap_weakening. Omega'.
Apply H1; Omega'. Omega'.
Decompose [exchange] Post15; Clear Post15.
Unfold array_id.
Intros i0 Hi0. Symmetry. Apply H17; Omega'.
Save.

Lemma heapsort_po_7 : 
  (N: Z)
  (t: (array N Z))
  (Pre16: `1 <= N`)
  (t0: (array N Z))
  (Post9: (heap t0 `N - 1` `0`) /\ (permut t0 t))
  (result0: Z)
  (Post6: result0 = `N - 1`)
  (Variant3: Z)
  (k0: Z)
  (t1: (array N Z))
  (Pre15: Variant3 = k0)
  (Pre14: (`0 <= k0` /\ `k0 <= N - 1`) /\
          ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
          ((`k0 + 1 <= N - 1` -> `(access t1 0) <= (access t1 k0 + 1)`)) /\
          ((`k0 + 1 <= N - 1` -> (sorted_array t1 `k0 + 1` `N - 1`))) /\
          (permut t1 t))
  (Test4: `k0 >= 1`)
  (Pre13: (`0 <= 0` /\ `0 < N`) /\ `0 <= k0` /\ `k0 < N`)
  (t2: (array N Z))
  (Post15: (exchange t2 t1 `0` k0))
  (Pre12: (`0 <= 0` /\ `0 <= k0 - 1`) /\ `k0 - 1 < N` /\
          ((i:Z) (`0 + 1 <= i` /\ `i <= k0 - 1` -> (heap t2 `k0 - 1` i))))
  (t3: (array N Z))
  (Post17: (permut t3 t2) /\
           ((i:Z) (`0 <= i` /\ `i <= k0 - 1` -> (heap t3 `k0 - 1` i))) /\
           ((i:Z)
            (`0 <= i` /\ `i < 0` \/ `0 < i` /\ `i < 2 * 0 + 1` \/
             `k0 - 1 < i` /\ `i < N` -> `(access t3 i) = (access t2 i)`)) /\
           ((v:Z)
            ((inftree t2 `k0 - 1` v `0`) -> (inftree t3 `k0 - 1` v `0`))))
  (k1: Z)
  (Post4: k1 = `k0 - 1`)
  ((`0 <= k1` /\ `k1 <= N - 1`) /\
  ((i:Z) (`0 <= i` /\ `i <= k1` -> (heap t3 k1 i))) /\
  ((`k1 + 1 <= N - 1` -> `(access t3 0) <= (access t3 k1 + 1)`)) /\
  ((`k1 + 1 <= N - 1` -> (sorted_array t3 `k1 + 1` `N - 1`))) /\
  (permut t3 t)) /\ (Zwf `0` k1 k0).
Proof.
Intuition.
(* heap *)
Subst k1; Apply H17; Omega'.
(* t[0] <= t[k] *)
Subst k1; Ring `k0-1+1`. 
Rewrite (H16 k0); [ Idtac | Omega' ].
Decompose [exchange] Post15.
Rewrite H23.
Apply inftree_1 with n:=`k0-1`.
Apply H19.
Apply inftree_weakening. Omega'.
Apply inftree_exchange with t1:=t1. Omega'.
Apply inftree_3.
Apply H1; Omega'.
Assumption. Omega'.
(* sorted *)
Subst k1; Ring `k0-1+1`.  
Elim (Z_le_lt_eq_dec k0 `N-1` H6); Intro.
  (* k0 < N-1 *)
  Replace k0 with `(k0+1)-1`; [ Idtac | Omega' ].
  Apply left_extension. Omega'. Omega'.
  Apply sorted_array_id with t1:=t2. 
  Apply sorted_array_id with t1:=t1. 
  Apply H7; Omega'.
  Decompose [exchange] Post15.
  Unfold array_id. Intros i Hi. Symmetry. Apply H24; Omega'.
  Unfold array_id. Intros i Hi. Symmetry. Apply H16; Omega'.
  (* t3[k0] <= t3[k0+1] *)
  Ring `k0+1-1`. 
  Rewrite (H16 k0); [ Idtac | Omega' ].
  Rewrite (H16 `k0+1`); [ Idtac | Omega' ].
  Decompose [exchange] Post15.
  Rewrite H23. Rewrite (H24 `k0+1`); [ Idtac | Omega' | Omega' | Omega' ].
  Apply H4; Omega'.
  (* k0 = N-1 *)
  Rewrite b. 
  Unfold sorted_array.
  Intros HN x HHx Hx. Absurd `x >= N-1`; Omega'.
(* (permut t3 t) *)
Apply permut_trans with t':=t2; Try Assumption. 
Apply permut_trans with t':=t1.
Apply exchange_is_permut with i:=`0` j:=k0. Assumption. 
Assumption. 
(* Zwf *)
Unfold Zwf; Omega'.
Save.

Lemma heapsort_po_8 : 
  (N: Z)
  (t: (array N Z))
  (Pre16: `1 <= N`)
  (t0: (array N Z))
  (Post9: (heap t0 `N - 1` `0`) /\ (permut t0 t))
  (result0: Z)
  (Post6: result0 = `N - 1`)
  (`0 <= result0` /\ `result0 <= N - 1`) /\
  ((i:Z) (`0 <= i` /\ `i <= result0` -> (heap t0 result0 i))) /\
  ((`result0 + 1 <= N - 1` -> `(access t0 0) <= (access t0 result0 + 1)`)) /\
  ((`result0 + 1 <= N - 1` -> (sorted_array t0 `result0 + 1` `N - 1`))) /\
  (permut t0 t).
Proof.
Intuition.
Apply heap_all.
Subst result0; Assumption.
Tauto.
Intro; Absurd `N-1+1 <= N-1`; Omega'.
Save.

Lemma heapsort_po_9 : 
  (N: Z)
  (t: (array N Z))
  (Pre16: `1 <= N`)
  (t0: (array N Z))
  (Post9: (heap t0 `N - 1` `0`) /\ (permut t0 t))
  (result0: Z)
  (Post6: result0 = `N - 1`)
  (k0: Z)
  (t1: (array N Z))
  (Post5: ((`0 <= k0` /\ `k0 <= N - 1`) /\
          ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
          ((`k0 + 1 <= N - 1` -> `(access t1 0) <= (access t1 k0 + 1)`)) /\
          ((`k0 + 1 <= N - 1` -> (sorted_array t1 `k0 + 1` `N - 1`))) /\
          (permut t1 t)) /\ `k0 < 1`)
  (sorted_array t1 `0` `N - 1`) /\ (permut t1 t).
Proof.
Intuition.
Elim (Z_le_lt_eq_dec `1` N Pre16); Intro.
  (* 1 < N *)
  Replace `0` with `1-1`; [ Idtac | Omega' ].
  Apply left_extension. Omega'. Omega'.
  Replace `1` with `k0+1`; [ Idtac | Omega' ].
  Replace `N-(k0+1)` with `N-1`; [ Idtac | Omega' ].
  Apply H6; Omega'.
  Replace `1-1` with `0`; [ Idtac | Omega' ]. (* Ring `1-1`. *)
  Replace `1` with `k0+1`; [ Idtac | Omega' ].
  Apply H4; Omega'.
  (* 1 = N *)
  Unfold sorted_array. 
  Intros HN x HHx Hx. Absurd `x >= N-1`; Omega'.
Save.

Require swap_why.
Require downheap_why.

Definition heapsort := (* validation *)
  [N: Z; t: (array N Z); Pre16: `1 <= N`]
    let (t0, result, Post9) =
      let (result, Post3) = (exist_1 [result: Z]
        result = (Zdiv2 `N - 2`) (Zdiv2 `N - 2`)
        (refl_equal ? (Zdiv2 `N - 2`))) in
      let (k0, t0, result0, Post2) =
        (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
          [Variant1: Z](k0: Z)(t0: (array N Z))(_: Variant1 = `k0 + 1`)
          (_0: (`(-1) <= k0` /\ `k0 <= N - 1`) /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= N - 1` -> (heap t0 `N - 1` i))) /\
          (permut t0 t))
          (sig_3 Z (array N Z) unit [k1: Z][t1: (array N Z)][result0: unit]
           (((`(-1) <= k1` /\ `k1 <= N - 1`) /\
           ((i:Z) (`k1 + 1 <= i` /\ `i <= N - 1` -> (heap t1 `N - 1` i))) /\
           (permut t1 t)) /\ `k1 < 0`))
          [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
           (k0: Z)(t0: (array N Z))(_: Variant2 = `k0 + 1`)
           (_0: (`(-1) <= k0` /\ `k0 <= N - 1`) /\
           ((i:Z) (`k0 + 1 <= i` /\ `i <= N - 1` -> (heap t0 `N - 1` i))) /\
           (permut t0 t))
           (sig_3 Z (array N Z) unit [k1: Z][t1: (array N Z)][result0: unit]
            (((`(-1) <= k1` /\ `k1 <= N - 1`) /\
            ((i:Z) (`k1 + 1 <= i` /\ `i <= N - 1` -> (heap t1 `N - 1` i))) /\
            (permut t1 t)) /\ `k1 < 0`));
           k0: Z; t0: (array N Z); Pre6: Variant1 = `k0 + 1`;
           Pre5: (`(-1) <= k0` /\ `k0 <= N - 1`) /\
           ((i:Z) (`k0 + 1 <= i` /\ `i <= N - 1` -> (heap t0 `N - 1` i))) /\
           (permut t0 t)]
            let (result0, Bool1) =
              let (result2, Post10) = (Z_ge_lt_bool k0 `0`) in
              (exist_1 [result3: bool]
              (if result3 then `k0 >= 0` else `k0 < 0`) result2 Post10) in
            (Cases (btest
                    [result0:bool](if result0 then `k0 >= 0` else `k0 < 0`)
                    result0 Bool1) of
            | (left Test2) =>
                let (k1, t1, result1, Post2) =
                  let (k1, t1, result1, Post8) =
                    let Pre4 =
                      (heapsort_po_1 N t Pre16 result Post3 Variant1 k0 t0
                      Pre6 Pre5 Test2) in
                    let (t1, result1, Post11) =
                      let Pre2 = Pre4 in
                      let Pre3 = Pre2 in
                      let (t1, result3, Post12) =
                        (downheap N k0 `N - 1` t0 Pre2) in
                      (exist_2 [t2: (array N Z)][result4: unit]
                      (permut t2 t0) /\
                      ((i:Z)
                       (`k0 <= i` /\ `i <= N - 1` -> (heap t2 `N - 1` i))) /\
                      ((i:Z)
                       (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                        `i < 2 * k0 + 1` \/ `N - 1 < i` /\ `i < N` ->
                        `(access t2 i) = (access t0 i)`)) /\
                      ((v:Z)
                       ((inftree t0 `N - 1` v k0) ->
                        (inftree t2 `N - 1` v k0))) t1
                      result3 Post12) in
                    let (k1, result2, Post1) =
                      let (result2, Post1) = (exist_1 [result2: Z]
                        result2 = `k0 - 1` `k0 - 1`
                        (refl_equal ? `k0 - 1`)) in
                      (exist_2 [k2: Z][result3: unit]k2 = `k0 - 1` result2 
                      tt Post1) in
                    (exist_3 [k2: Z][t2: (array N Z)][result3: unit]
                    ((`(-1) <= k2` /\ `k2 <= N - 1`) /\
                    ((i:Z)
                     (`k2 + 1 <= i` /\ `i <= N - 1` -> (heap t2 `N - 1` i))) /\
                    (permut t2 t)) /\ (Zwf `0` `k2 + 1` `k0 + 1`) k1 
                    t1 result2
                    (heapsort_po_2 N t Pre16 result Post3 Variant1 k0 t0 Pre6
                    Pre5 Test2 Pre4 t1 Post11 k1 Post1)) in
                  ((wf1 `k1 + 1`) (loop_variant_1 Pre6 Post8) k1 t1
                    (refl_equal ? `k1 + 1`) (proj1 ? ? Post8)) in
                (exist_3 [k2: Z][t2: (array N Z)][result2: unit]
                ((`(-1) <= k2` /\ `k2 <= N - 1`) /\
                ((i:Z) (`k2 + 1 <= i` /\ `i <= N - 1` -> (heap t2 `N - 1` i))) /\
                (permut t2 t)) /\ `k2 < 0` k1 t1 result1 Post2)
            | (right Test1) =>
                let (k1, t1, result1, Post2) = (exist_3 [k1: Z]
                  [t1: (array N Z)][result1: unit]((`(-1) <= k1` /\
                  `k1 <= N - 1`) /\
                  ((i:Z)
                   (`k1 + 1 <= i` /\ `i <= N - 1` -> (heap t1 `N - 1` i))) /\
                  (permut t1 t)) /\ `k1 < 0` k0 t0 tt
                  (conj ? ? Pre5 Test1)) in
                (exist_3 [k2: Z][t2: (array N Z)][result2: unit]
                ((`(-1) <= k2` /\ `k2 <= N - 1`) /\
                ((i:Z) (`k2 + 1 <= i` /\ `i <= N - 1` -> (heap t2 `N - 1` i))) /\
                (permut t2 t)) /\ `k2 < 0` k1 t1 result1 Post2) end)
          `result + 1` result t (refl_equal ? `result + 1`)
          (heapsort_po_3 N t Pre16 result Post3)) in
      (exist_2 [t1: (array N Z)][result1: unit](heap t1 `N - 1` `0`) /\
      (permut t1 t) t0 result0
      (heapsort_po_4 N t Pre16 result Post3 k0 t0 Post2)) in
    let (t1, result0, Post13) =
      let (result0, Post6) = (exist_1 [result0: Z]result0 = `N - 1` `N - 1`
        (refl_equal ? `N - 1`)) in
      let (k0, t1, result1, Post5) =
        (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
          [Variant3: Z](k0: Z)(t1: (array N Z))(_: Variant3 = k0)
          (_0: (`0 <= k0` /\ `k0 <= N - 1`) /\
          ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
          ((`k0 + 1 <= N - 1` -> `(access t1 0) <= (access t1 k0 + 1)`)) /\
          ((`k0 + 1 <= N - 1` -> (sorted_array t1 `k0 + 1` `N - 1`))) /\
          (permut t1 t))
          (sig_3 Z (array N Z) unit [k1: Z][t2: (array N Z)][result1: unit]
           (((`0 <= k1` /\ `k1 <= N - 1`) /\
           ((i:Z) (`0 <= i` /\ `i <= k1` -> (heap t2 k1 i))) /\
           ((`k1 + 1 <= N - 1` -> `(access t2 0) <= (access t2 k1 + 1)`)) /\
           ((`k1 + 1 <= N - 1` -> (sorted_array t2 `k1 + 1` `N - 1`))) /\
           (permut t2 t)) /\ `k1 < 1`))
          [Variant3: Z; wf2: (Variant4: Z)(Pre7: (Zwf `0` Variant4 Variant3))
           (k0: Z)(t1: (array N Z))(_: Variant4 = k0)(_0: (`0 <= k0` /\
           `k0 <= N - 1`) /\
           ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
           ((`k0 + 1 <= N - 1` -> `(access t1 0) <= (access t1 k0 + 1)`)) /\
           ((`k0 + 1 <= N - 1` -> (sorted_array t1 `k0 + 1` `N - 1`))) /\
           (permut t1 t))
           (sig_3 Z (array N Z) unit [k1: Z][t2: (array N Z)][result1: unit]
            (((`0 <= k1` /\ `k1 <= N - 1`) /\
            ((i:Z) (`0 <= i` /\ `i <= k1` -> (heap t2 k1 i))) /\
            ((`k1 + 1 <= N - 1` -> `(access t2 0) <= (access t2 k1 + 1)`)) /\
            ((`k1 + 1 <= N - 1` -> (sorted_array t2 `k1 + 1` `N - 1`))) /\
            (permut t2 t)) /\ `k1 < 1`));
           k0: Z; t1: (array N Z); Pre15: Variant3 = k0; Pre14: (`0 <= k0` /\
           `k0 <= N - 1`) /\
           ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
           ((`k0 + 1 <= N - 1` -> `(access t1 0) <= (access t1 k0 + 1)`)) /\
           ((`k0 + 1 <= N - 1` -> (sorted_array t1 `k0 + 1` `N - 1`))) /\
           (permut t1 t)]
            let (result1, Bool2) =
              let (result3, Post14) = (Z_ge_lt_bool k0 `1`) in
              (exist_1 [result4: bool]
              (if result4 then `k0 >= 1` else `k0 < 1`) result3 Post14) in
            (Cases (btest
                    [result1:bool](if result1 then `k0 >= 1` else `k0 < 1`)
                    result1 Bool2) of
            | (left Test4) =>
                let (k1, t2, result2, Post5) =
                  let (k1, t2, result2, Post7) =
                    let Pre13 =
                      (heapsort_po_5 N t Pre16 t0 Post9 result0 Post6
                      Variant3 k0 t1 Pre15 Pre14 Test4) in
                    let (t2, result2, Post15) =
                      let Pre8 = Pre13 in
                      let Pre9 = Pre8 in
                      let (t2, result4, Post16) = (swap N `0` k0 t1 Pre8) in
                      (exist_2 [t3: (array N Z)][result5: unit]
                      (exchange t3 t1 `0` k0) t2 result4 Post16) in
                    let Pre12 =
                      (heapsort_po_6 N t Pre16 t0 Post9 result0 Post6
                      Variant3 k0 t1 Pre15 Pre14 Test4 Pre13 t2 Post15) in
                    let (t3, result3, Post17) =
                      let Pre10 = Pre12 in
                      let Pre11 = Pre10 in
                      let (t3, result5, Post18) =
                        (downheap N `0` `k0 - 1` t2 Pre10) in
                      (exist_2 [t4: (array N Z)][result6: unit]
                      (permut t4 t2) /\
                      ((i:Z)
                       (`0 <= i` /\ `i <= k0 - 1` -> (heap t4 `k0 - 1` i))) /\
                      ((i:Z)
                       (`0 <= i` /\ `i < 0` \/ `0 < i` /\ `i < 2 * 0 + 1` \/
                        `k0 - 1 < i` /\ `i < N` ->
                        `(access t4 i) = (access t2 i)`)) /\
                      ((v:Z)
                       ((inftree t2 `k0 - 1` v `0`) ->
                        (inftree t4 `k0 - 1` v `0`))) t3
                      result5 Post18) in
                    let (k1, result4, Post4) =
                      let (result4, Post4) = (exist_1 [result4: Z]
                        result4 = `k0 - 1` `k0 - 1`
                        (refl_equal ? `k0 - 1`)) in
                      (exist_2 [k2: Z][result5: unit]k2 = `k0 - 1` result4 
                      tt Post4) in
                    (exist_3 [k2: Z][t4: (array N Z)][result5: unit]
                    ((`0 <= k2` /\ `k2 <= N - 1`) /\
                    ((i:Z) (`0 <= i` /\ `i <= k2` -> (heap t4 k2 i))) /\
                    ((`k2 + 1 <= N - 1` ->
                      `(access t4 0) <= (access t4 k2 + 1)`)) /\
                    ((`k2 + 1 <= N - 1` -> (sorted_array t4 `k2 + 1` `N - 1`))) /\
                    (permut t4 t)) /\ (Zwf `0` k2 k0) k1 t3 result4
                    (heapsort_po_7 N t Pre16 t0 Post9 result0 Post6 Variant3
                    k0 t1 Pre15 Pre14 Test4 Pre13 t2 Post15 Pre12 t3 Post17
                    k1 Post4)) in
                  ((wf2 k1) (loop_variant_1 Pre15 Post7) k1 t2
                    (refl_equal ? k1) (proj1 ? ? Post7)) in
                (exist_3 [k2: Z][t3: (array N Z)][result3: unit]
                ((`0 <= k2` /\ `k2 <= N - 1`) /\
                ((i:Z) (`0 <= i` /\ `i <= k2` -> (heap t3 k2 i))) /\
                ((`k2 + 1 <= N - 1` -> `(access t3 0) <= (access t3 k2 + 1)`)) /\
                ((`k2 + 1 <= N - 1` -> (sorted_array t3 `k2 + 1` `N - 1`))) /\
                (permut t3 t)) /\ `k2 < 1` k1 t2 result2 Post5)
            | (right Test3) =>
                let (k1, t2, result2, Post5) = (exist_3 [k1: Z]
                  [t2: (array N Z)][result2: unit]((`0 <= k1` /\
                  `k1 <= N - 1`) /\
                  ((i:Z) (`0 <= i` /\ `i <= k1` -> (heap t2 k1 i))) /\
                  ((`k1 + 1 <= N - 1` ->
                    `(access t2 0) <= (access t2 k1 + 1)`)) /\
                  ((`k1 + 1 <= N - 1` -> (sorted_array t2 `k1 + 1` `N - 1`))) /\
                  (permut t2 t)) /\ `k1 < 1` k0 t1 tt
                  (conj ? ? Pre14 Test3)) in
                (exist_3 [k2: Z][t3: (array N Z)][result3: unit]
                ((`0 <= k2` /\ `k2 <= N - 1`) /\
                ((i:Z) (`0 <= i` /\ `i <= k2` -> (heap t3 k2 i))) /\
                ((`k2 + 1 <= N - 1` -> `(access t3 0) <= (access t3 k2 + 1)`)) /\
                ((`k2 + 1 <= N - 1` -> (sorted_array t3 `k2 + 1` `N - 1`))) /\
                (permut t3 t)) /\ `k2 < 1` k1 t2 result2 Post5) end) 
          result0 result0 t0 (refl_equal ? result0)
          (heapsort_po_8 N t Pre16 t0 Post9 result0 Post6)) in
      (exist_2 [t2: (array N Z)][result2: unit]
      (sorted_array t2 `0` `N - 1`) /\ (permut t2 t) t1 result1
      (heapsort_po_9 N t Pre16 t0 Post9 result0 Post6 k0 t1 Post5)) in
    (exist_2 [t2: (array N Z)][result1: unit](sorted_array t2 `0` `N - 1`) /\
    (permut t2 t) t1 result0 Post13).

