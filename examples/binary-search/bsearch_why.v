
Require Why.
Require ZArith.
Require Zcomplements.
Require Omega. 

Tactic Definition Omega' := Abstract Omega.

(* Parameters and axioms *)

(*Why*) Parameter N : Z.

Axiom N_positive : `N >= 0`.

(*Why*) Parameter v : Z.

(* Specification *)

Inductive In [t:(array (Zs N) Z); l,u:Z] : Prop :=
  In_cons : (i:Z) `l <= i <= u` -> #t[i]=v -> (In t l u).

Definition mean := [x,y:Z](Zdiv2 `x+y`).

(* Lemmas *)

Lemma le_mean : (x,y:Z)
  `0 <= x <= y` -> `x <= (mean x y)`.
Proof.
Intros.
Apply Zle_Zmult_right2 with z:=`2`.
Omega.
Rewrite Zmult_sym.
Rewrite (Zmult_sym (mean x y) `2`).
Unfold mean.
Elim (Zeven_odd_dec `x+y`); Intro.
Rewrite <- Zeven_div2 with `x+y`.
Omega.
Assumption.
Elim (Z_eq_dec x y); Intro.
Absurd x=y; Try Assumption.
Rewrite a in b.
Absurd (Zodd `y+y`); Try Assumption.
Absurd `y+y = 2*(Zdiv2 (y+y))+1`.
Omega.
Apply Zodd_div2.
Omega.
Assumption.
Cut `x+y = 2*(Zdiv2 (x+y))+1`.
Omega.
Apply Zodd_div2.
Omega.
Assumption.
Save.

Lemma ge_mean : (x,y:Z)
  `0 <= x <= y` -> `(mean x y) <= y`.
Proof.
Intros.
Apply Zle_Zmult_right2 with z:=`2`.
Omega.
Rewrite Zmult_sym.
Rewrite (Zmult_sym y `2`).
Unfold mean.
Elim (Zeven_odd_dec `x+y`); Intro.
Rewrite <- Zeven_div2 with `x+y`.
Omega.
Assumption.
Cut `x+y = 2*(Zdiv2 (x+y))+1`.
Omega.
Apply Zodd_div2.
Omega.
Assumption.
Save.

Lemma In_right_side : (t:(array (Zs N) Z))
  (sorted_array t `1` N) ->
  (l,u:Z)
  `1 <= l` -> `u <= N` -> `l <= u` -> `l <= (mean l u) <= u` ->
  ((In t `1` N) -> (In t l u)) ->
  `(access t (mean l u)) < v` ->
  ((In t `1` N) -> (In t `(mean l u)+1` u)).
Proof.     
Intros t Hsorted l u Hl Hu Hlu Hm Inv Hv H.
Generalize (Inv H). Intro.
Decompose [In] H0.
Apply In_cons with i.
Elim (Z_gt_le_dec `(mean l u)+1` i); Intro.
Absurd (access t i)=v.
Apply Zlt_not_eq.
Apply Zle_lt_trans with (access t (mean l u)).
Apply sorted_elements with n:=`1` m:=N.
Assumption.
Omega'.
Omega'.
Omega'.
Omega'.
Assumption.
Assumption.
Omega'.
Assumption.
Save.

Lemma In_left_side : (t:(array (Zs N) Z))
  (sorted_array t `1` N) ->
  (l,u:Z)
  `1 <= l` -> `u <= N` -> `l <= u` -> `l <= (mean l u) <= u` ->
  ((In t `1` N) -> (In t l u)) ->
  `(access t (mean l u)) > v` ->
  ((In t `1` N) -> (In t l `(mean l u)-1`)).
Proof.     
Intros t Hsorted l u Hl Hu Hlu Hm Inv Hv H.
Generalize (Inv H). Intro.
Decompose [In] H0.
Apply In_cons with i.
Elim (Z_gt_le_dec i `(mean l u)-1`); Intro.
Absurd (access t i)=v.
Apply sym_not_eq.
Apply Zlt_not_eq.
Apply Zlt_le_trans with (access t (mean l u)).
Omega'.
Apply sorted_elements with n:=`1` m:=N.
Assumption.
Omega'.
Omega'.
Omega'.
Omega'.
Assumption.
Omega'.
Assumption.
Save.

(* Obligations *)

Lemma binary_search_po_1 : 
  (t: (array `N + 1` Z))
  (Pre7: (sorted_array t `1` N))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = N)
  (p0: Z)
  (Post3: p0 = `0`)
  (well_founded ? (Zwf ZERO)).
Proof. Auto with *. Save.

Lemma binary_search_po_2 : 
  (t: (array `N + 1` Z))
  (Pre7: (sorted_array t `1` N))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = N)
  (p0: Z)
  (Post3: p0 = `0`)
  (Variant1: Z)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Pre6: Variant1 = `2 + u1 - l1`)
  (Pre5: `1 <= l1` /\ `u1 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
         ((`p1 = 0` -> ((In t `1` N) -> (In t l1 u1)))) /\
         ((`p1 > 0` -> `(access t p1) = v`)))
  (Test6: `l1 <= u1`)
  (m1: Z)
  (Post4: m1 = (mean l1 u1))
  `l1 <= m1` /\ `m1 <= u1`.
Proof.
Intros.
Clear Pre8; Simpl in Test6.
Split. Rewrite Post4; Apply le_mean; Omega'.
Rewrite Post4; Apply ge_mean; Omega'.
Save.

Lemma binary_search_po_3 : 
  (t: (array `N + 1` Z))
  (Pre7: (sorted_array t `1` N))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = N)
  (p0: Z)
  (Post3: p0 = `0`)
  (Variant1: Z)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Pre6: Variant1 = `2 + u1 - l1`)
  (Pre5: `1 <= l1` /\ `u1 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
         ((`p1 = 0` -> ((In t `1` N) -> (In t l1 u1)))) /\
         ((`p1 > 0` -> `(access t p1) = v`)))
  (Test6: `l1 <= u1`)
  (m1: Z)
  (Post4: m1 = (mean l1 u1))
  (Pre4: `l1 <= m1` /\ `m1 <= u1`)
  `0 <= m1` /\ `m1 < N + 1`.
Proof.
Intros.
Clear Pre8.
Omega'.
Save.

Lemma binary_search_po_4 : 
  (t: (array `N + 1` Z))
  (Pre7: (sorted_array t `1` N))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = N)
  (p0: Z)
  (Post3: p0 = `0`)
  (Variant1: Z)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Pre6: Variant1 = `2 + u1 - l1`)
  (Pre5: `1 <= l1` /\ `u1 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
         ((`p1 = 0` -> ((In t `1` N) -> (In t l1 u1)))) /\
         ((`p1 > 0` -> `(access t p1) = v`)))
  (Test6: `l1 <= u1`)
  (m1: Z)
  (Post4: m1 = (mean l1 u1))
  (Pre4: `l1 <= m1` /\ `m1 <= u1`)
  (Test5: `(access t m1) < v`)
  (l2: Z)
  (Post8: l2 = `m1 + 1`)
  (`1 <= l2` /\ `u1 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
  ((`p1 = 0` -> ((In t `1` N) -> (In t l2 u1)))) /\
  ((`p1 > 0` -> `(access t p1) = v`))) /\
  (Zwf `0` `2 + u1 - l2` `2 + u1 - l1`).
Proof.
Intros.
Repeat Split; Try Omega'.
Rewrite Post8; Clear Post8; Rewrite Post4.
Intros; Apply In_right_side; Assumption Orelse Intuition.
Rewrite <- Post4; Assumption.
Save.

Lemma binary_search_po_5 : 
  (t: (array `N + 1` Z))
  (Pre7: (sorted_array t `1` N))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = N)
  (p0: Z)
  (Post3: p0 = `0`)
  (Variant1: Z)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Pre6: Variant1 = `2 + u1 - l1`)
  (Pre5: `1 <= l1` /\ `u1 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
         ((`p1 = 0` -> ((In t `1` N) -> (In t l1 u1)))) /\
         ((`p1 > 0` -> `(access t p1) = v`)))
  (Test6: `l1 <= u1`)
  (m1: Z)
  (Post4: m1 = (mean l1 u1))
  (Pre4: `l1 <= m1` /\ `m1 <= u1`)
  (Test4: `(access t m1) >= v`)
  `0 <= m1` /\ `m1 < N + 1`.
Proof.
Intros.
Clear Pre6; Simpl in Test6.
Simpl in Test4.
Repeat Split; Try Omega'.
Save.

Lemma binary_search_po_6 : 
  (t: (array `N + 1` Z))
  (Pre7: (sorted_array t `1` N))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = N)
  (p0: Z)
  (Post3: p0 = `0`)
  (Variant1: Z)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Pre6: Variant1 = `2 + u1 - l1`)
  (Pre5: `1 <= l1` /\ `u1 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
         ((`p1 = 0` -> ((In t `1` N) -> (In t l1 u1)))) /\
         ((`p1 > 0` -> `(access t p1) = v`)))
  (Test6: `l1 <= u1`)
  (m1: Z)
  (Post4: m1 = (mean l1 u1))
  (Pre4: `l1 <= m1` /\ `m1 <= u1`)
  (Test4: `(access t m1) >= v`)
  (Test3: `(access t m1) > v`)
  (u2: Z)
  (Post7: u2 = `m1 - 1`)
  (`1 <= l1` /\ `u2 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
  ((`p1 = 0` -> ((In t `1` N) -> (In t l1 u2)))) /\
  ((`p1 > 0` -> `(access t p1) = v`))) /\
  (Zwf `0` `2 + u2 - l1` `2 + u1 - l1`).
Proof.
Intros.
Clear Pre6; Simpl in Test6.
Simpl in Test4.
Simpl in Test3.
Repeat Split; Try Omega'.
Rewrite Post7; Clear Post7; Rewrite Post4.
Intros; Apply In_left_side; Assumption Orelse Intuition.
Rewrite <- Post4; Assumption.
Save.

Lemma binary_search_po_7 : 
  (t: (array `N + 1` Z))
  (Pre7: (sorted_array t `1` N))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = N)
  (p0: Z)
  (Post3: p0 = `0`)
  (Variant1: Z)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Pre6: Variant1 = `2 + u1 - l1`)
  (Pre5: `1 <= l1` /\ `u1 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
         ((`p1 = 0` -> ((In t `1` N) -> (In t l1 u1)))) /\
         ((`p1 > 0` -> `(access t p1) = v`)))
  (Test6: `l1 <= u1`)
  (m1: Z)
  (Post4: m1 = (mean l1 u1))
  (Pre4: `l1 <= m1` /\ `m1 <= u1`)
  (Test4: `(access t m1) >= v`)
  (Test2: `(access t m1) <= v`)
  (p2: Z)
  (Post5: p2 = m1)
  (l2: Z)
  (Post6: l2 = `u1 + 1`)
  (`1 <= l2` /\ `u1 <= N` /\ (`0 <= p2` /\ `p2 <= N`) /\
  ((`p2 = 0` -> ((In t `1` N) -> (In t l2 u1)))) /\
  ((`p2 > 0` -> `(access t p2) = v`))) /\
  (Zwf `0` `2 + u1 - l2` `2 + u1 - l1`).
Proof.
Intros.
Clear Pre8; Simpl in Test6.
Simpl in Test4.
Simpl in Test2.
Repeat Split; Try Omega'.
Intros; Absurd `p2 = 0`; Omega'.
Intro; Rewrite Post5; Omega'.
Save.

Lemma binary_search_po_8 : 
  (t: (array `N + 1` Z))
  (Pre7: (sorted_array t `1` N))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = N)
  (p0: Z)
  (Post3: p0 = `0`)
  (Variant1: Z)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Pre6: Variant1 = `2 + u1 - l1`)
  (Pre5: `1 <= l1` /\ `u1 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
         ((`p1 = 0` -> ((In t `1` N) -> (In t l1 u1)))) /\
         ((`p1 > 0` -> `(access t p1) = v`)))
  (Test6: `l1 <= u1`)
  (l2: Z)
  (p2: Z)
  (u2: Z)
  (Post10: (`1 <= l2` /\ `u2 <= N` /\ (`0 <= p2` /\ `p2 <= N`) /\
           ((`p2 = 0` -> ((In t `1` N) -> (In t l2 u2)))) /\
           ((`p2 > 0` -> `(access t p2) = v`))) /\
           (Zwf `0` `2 + u2 - l2` `2 + u1 - l1`))
  (Zwf `0` `2 + u2 - l2` Variant1).
Proof.
Intros.
Rewrite Pre6; Tauto.
Save.

Lemma binary_search_po_9 : 
  (t: (array `N + 1` Z))
  (Pre7: (sorted_array t `1` N))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = N)
  (p0: Z)
  (Post3: p0 = `0`)
  `1 <= l0` /\ `u0 <= N` /\ (`0 <= p0` /\ `p0 <= N`) /\
  ((`p0 = 0` -> ((In t `1` N) -> (In t l0 u0)))) /\
  ((`p0 > 0` -> `(access t p0) = v`)).
Proof.
Intuition.
Generalize N_positive; Intro.
Repeat Split; Intros; Try Omega'.
Rewrite Post1; Rewrite Post2; Assumption.
Save.

Lemma binary_search_po_10 : 
  (t: (array `N + 1` Z))
  (Pre7: (sorted_array t `1` N))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = N)
  (p0: Z)
  (Post3: p0 = `0`)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Post9: (`1 <= l1` /\ `u1 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
          ((`p1 = 0` -> ((In t `1` N) -> (In t l1 u1)))) /\
          ((`p1 > 0` -> `(access t p1) = v`))) /\ `l1 > u1`)
  (`1 <= p1` /\ `p1 <= N`) /\ `(access t p1) = v` \/ `p1 = 0` /\
  ~(In t `1` N).
Proof.
Intros.
Intuition.
Elim (Z_lt_ge_dec `0` p1); Intro.
Left; Omega'.
Right. 
Cut `p1 = 0`; [ Intro | Omega' ].
Split. Assumption.
Intro. 
Generalize (H2 H4 H7); Intro.
Decompose [In] H8.
Absurd `l1 <= i <= u1`; Omega'.
Save.

Definition binary_search := (* validation *)
  [l: Z; m: Z; p: Z; t: (array `N + 1` Z); u: Z; Pre7: (sorted_array t `1` N)]
    let (l0, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
        (refl_equal ? `1`)) in
      (exist_2 [l1: Z][result0: unit]l1 = `1` result tt Post1) in
    let (u0, result0, Post2) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = N N
        (refl_equal ? N)) in
      (exist_2 [u1: Z][result1: unit]u1 = N result0 tt Post2) in
    let (p0, result1, Post3) =
      let (result1, Post3) = (exist_1 [result1: Z]result1 = `0` `0`
        (refl_equal ? `0`)) in
      (exist_2 [p1: Z][result2: unit]p1 = `0` result1 tt Post3) in
    let (l1, m0, p1, u1, result2, Post9) =
      (well_founded_induction Z (Zwf ZERO)
        (binary_search_po_1 t Pre7 l0 Post1 u0 Post2 p0 Post3) [Variant1: Z]
        (l1: Z)(m0: Z)(p1: Z)(u1: Z)(_: Variant1 = `2 + u1 - l1`)
        (_0: `1 <= l1` /\ `u1 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
        ((`p1 = 0` -> ((In t `1` N) -> (In t l1 u1)))) /\
        ((`p1 > 0` -> `(access t p1) = v`)))
        (sig_5 Z Z Z Z unit [l2: Z][m1: Z][p2: Z][u2: Z][result2: unit]
         ((`1 <= l2` /\ `u2 <= N` /\ (`0 <= p2` /\ `p2 <= N`) /\
         ((`p2 = 0` -> ((In t `1` N) -> (In t l2 u2)))) /\
         ((`p2 > 0` -> `(access t p2) = v`))) /\ `l2 > u2`))
        [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
         (l1: Z)(m0: Z)(p1: Z)(u1: Z)(_: Variant2 = `2 + u1 - l1`)
         (_0: `1 <= l1` /\ `u1 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
         ((`p1 = 0` -> ((In t `1` N) -> (In t l1 u1)))) /\
         ((`p1 > 0` -> `(access t p1) = v`)))
         (sig_5 Z Z Z Z unit [l2: Z][m1: Z][p2: Z][u2: Z][result2: unit]
          ((`1 <= l2` /\ `u2 <= N` /\ (`0 <= p2` /\ `p2 <= N`) /\
          ((`p2 = 0` -> ((In t `1` N) -> (In t l2 u2)))) /\
          ((`p2 > 0` -> `(access t p2) = v`))) /\ `l2 > u2`));
         l1: Z; m0: Z; p1: Z; u1: Z; Pre6: Variant1 = `2 + u1 - l1`;
         Pre5: `1 <= l1` /\ `u1 <= N` /\ (`0 <= p1` /\ `p1 <= N`) /\
         ((`p1 = 0` -> ((In t `1` N) -> (In t l1 u1)))) /\
         ((`p1 > 0` -> `(access t p1) = v`))]
          let (result2, Bool1) =
            let (result4, Post13) = (Z_le_gt_bool l1 u1) in
            (exist_1 [result5: bool]
            (if result5 then `l1 <= u1` else `l1 > u1`) result4 Post13) in
          (Cases (btest
                  [result2:bool](if result2 then `l1 <= u1` else `l1 > u1`)
                  result2 Bool1) of
          | (left Test6) =>
              let (l2, m1, p2, u2, result3, Post9) =
                let (l2, m1, p2, u2, result3, Post10) =
                  let (m1, result3, Post4) =
                    let (result3, Post4) = (exist_1 [result3: Z]
                      result3 = (mean l1 u1) (mean l1 u1)
                      (refl_equal ? (mean l1 u1))) in
                    (exist_2 [m2: Z][result4: unit]m2 = (mean l1 u1) 
                    result3 tt Post4) in
                  let Pre4 =
                    (binary_search_po_2 t Pre7 l0 Post1 u0 Post2 p0 Post3
                    Variant1 l1 p1 u1 Pre6 Pre5 Test6 m1 Post4) in
                  let (l2, p2, u2, result4, Post10) =
                    let (result4, Bool3) =
                      let result5 =
                        let Pre2 =
                          (binary_search_po_3 t Pre7 l0 Post1 u0 Post2 p0
                          Post3 Variant1 l1 p1 u1 Pre6 Pre5 Test6 m1 Post4
                          Pre4) in
                        (Z_lt_ge_bool (access t m1)) in
                      let (result6, Post14) = (result5 v) in
                      (exist_1 [result7: bool]
                      (if result7 then `(access t m1) < v`
                       else `(access t m1) >= v`) result6
                      Post14) in
                    (Cases (btest
                            [result4:bool](if result4
                                           then `(access t m1) < v`
                                           else `(access t m1) >= v`)
                            result4 Bool3) of
                    | (left Test5) =>
                        let (l2, result5, Post8) =
                          let (result5, Post8) = (exist_1 [result5: Z]
                            result5 = `m1 + 1` `m1 + 1`
                            (refl_equal ? `m1 + 1`)) in
                          (exist_2 [l3: Z][result6: unit]
                          l3 = `m1 + 1` result5 tt Post8) in
                        (exist_4 [l3: Z][p2: Z][u2: Z][result6: unit]
                        (`1 <= l3` /\ `u2 <= N` /\ (`0 <= p2` /\
                        `p2 <= N`) /\
                        ((`p2 = 0` -> ((In t `1` N) -> (In t l3 u2)))) /\
                        ((`p2 > 0` -> `(access t p2) = v`))) /\
                        (Zwf `0` `2 + u2 - l3` `2 + u1 - l1`) l2 p1 u1
                        result5
                        (binary_search_po_4 t Pre7 l0 Post1 u0 Post2 p0 Post3
                        Variant1 l1 p1 u1 Pre6 Pre5 Test6 m1 Post4 Pre4 Test5
                        l2 Post8))
                    | (right Test4) =>
                        let (l2, p2, u2, result5, Post10) =
                          let (result5, Bool2) =
                            let result6 =
                              let Pre3 =
                                (binary_search_po_5 t Pre7 l0 Post1 u0 Post2
                                p0 Post3 Variant1 l1 p1 u1 Pre6 Pre5 Test6 m1
                                Post4 Pre4 Test4) in
                              (Z_gt_le_bool (access t m1)) in
                            let (result7, Post15) = (result6 v) in
                            (exist_1 [result8: bool]
                            (if result8 then `(access t m1) > v`
                             else `(access t m1) <= v`) result7
                            Post15) in
                          (Cases (btest
                                  [result5:bool](if result5
                                                 then `(access t m1) > v`
                                                 else `(access t m1) <= v`)
                                  result5 Bool2) of
                          | (left Test3) =>
                              let (u2, result6, Post7) =
                                let (result6, Post7) = (exist_1 [result6: Z]
                                  result6 = `m1 - 1` `m1 - 1`
                                  (refl_equal ? `m1 - 1`)) in
                                (exist_2 [u3: Z][result7: unit]
                                u3 = `m1 - 1` result6 tt Post7) in
                              (exist_4 [l2: Z][p2: Z][u3: Z][result7: unit]
                              (`1 <= l2` /\ `u3 <= N` /\ (`0 <= p2` /\
                              `p2 <= N`) /\
                              ((`p2 = 0` -> ((In t `1` N) -> (In t l2 u3)))) /\
                              ((`p2 > 0` -> `(access t p2) = v`))) /\
                              (Zwf `0` `2 + u3 - l2` `2 + u1 - l1`) l1 
                              p1 u2 result6
                              (binary_search_po_6 t Pre7 l0 Post1 u0 Post2 p0
                              Post3 Variant1 l1 p1 u1 Pre6 Pre5 Test6 m1
                              Post4 Pre4 Test4 Test3 u2 Post7))
                          | (right Test2) =>
                              let (l2, p2, result6, Post10) =
                                let (p2, result6, Post5) =
                                  let (result6, Post5) =
                                    (exist_1 [result6: Z]result6 = m1 
                                    m1 (refl_equal ? m1)) in
                                  (exist_2 [p3: Z][result7: unit]
                                  p3 = m1 result6 tt Post5) in
                                let (l2, result7, Post6) =
                                  let (result7, Post6) =
                                    (exist_1 [result7: Z]
                                    result7 = `u1 + 1` `u1 + 1`
                                    (refl_equal ? `u1 + 1`)) in
                                  (exist_2 [l3: Z][result8: unit]
                                  l3 = `u1 + 1` result7 tt Post6) in
                                (exist_3 [l3: Z][p3: Z][result8: unit]
                                (`1 <= l3` /\ `u1 <= N` /\ (`0 <= p3` /\
                                `p3 <= N`) /\
                                ((`p3 = 0` -> ((In t `1` N) -> (In t l3 u1)))) /\
                                ((`p3 > 0` -> `(access t p3) = v`))) /\
                                (Zwf `0` `2 + u1 - l3` `2 + u1 - l1`) 
                                l2 p2 result7
                                (binary_search_po_7 t Pre7 l0 Post1 u0 Post2
                                p0 Post3 Variant1 l1 p1 u1 Pre6 Pre5 Test6 m1
                                Post4 Pre4 Test4 Test2 p2 Post5 l2 Post6)) in
                              (exist_4 [l3: Z][p3: Z][u2: Z][result7: unit]
                              (`1 <= l3` /\ `u2 <= N` /\ (`0 <= p3` /\
                              `p3 <= N`) /\
                              ((`p3 = 0` -> ((In t `1` N) -> (In t l3 u2)))) /\
                              ((`p3 > 0` -> `(access t p3) = v`))) /\
                              (Zwf `0` `2 + u2 - l3` `2 + u1 - l1`) l2 
                              p2 u1 result6 Post10) end) in
                        (exist_4 [l3: Z][p3: Z][u3: Z][result6: unit]
                        (`1 <= l3` /\ `u3 <= N` /\ (`0 <= p3` /\
                        `p3 <= N`) /\
                        ((`p3 = 0` -> ((In t `1` N) -> (In t l3 u3)))) /\
                        ((`p3 > 0` -> `(access t p3) = v`))) /\
                        (Zwf `0` `2 + u3 - l3` `2 + u1 - l1`) l2 p2 u2
                        result5 Post10) end) in
                  (exist_5 [l3: Z][m2: Z][p3: Z][u3: Z][result5: unit]
                  (`1 <= l3` /\ `u3 <= N` /\ (`0 <= p3` /\ `p3 <= N`) /\
                  ((`p3 = 0` -> ((In t `1` N) -> (In t l3 u3)))) /\
                  ((`p3 > 0` -> `(access t p3) = v`))) /\
                  (Zwf `0` `2 + u3 - l3` `2 + u1 - l1`) l2 m1 p2 u2 result4
                  Post10) in
                ((wf1 `2 + u2 - l2`)
                  (binary_search_po_8 t Pre7 l0 Post1 u0 Post2 p0 Post3
                  Variant1 l1 p1 u1 Pre6 Pre5 Test6 l2 p2 u2 Post10) 
                  l2 m1 p2 u2 (refl_equal ? `2 + u2 - l2`)
                  (proj1 ? ? Post10)) in
              (exist_5 [l3: Z][m2: Z][p3: Z][u3: Z][result4: unit]
              (`1 <= l3` /\ `u3 <= N` /\ (`0 <= p3` /\ `p3 <= N`) /\
              ((`p3 = 0` -> ((In t `1` N) -> (In t l3 u3)))) /\
              ((`p3 > 0` -> `(access t p3) = v`))) /\ `l3 > u3` l2 m1 
              p2 u2 result3 Post9)
          | (right Test1) =>
              let (l2, m1, p2, u2, result3, Post9) = (exist_5 [l2: Z][m1: Z]
                [p2: Z][u2: Z][result3: unit](`1 <= l2` /\ `u2 <= N` /\
                (`0 <= p2` /\ `p2 <= N`) /\
                ((`p2 = 0` -> ((In t `1` N) -> (In t l2 u2)))) /\
                ((`p2 > 0` -> `(access t p2) = v`))) /\ `l2 > u2` l1 
                m0 p1 u1 tt (conj ? ? Pre5 Test1)) in
              (exist_5 [l3: Z][m2: Z][p3: Z][u3: Z][result4: unit]
              (`1 <= l3` /\ `u3 <= N` /\ (`0 <= p3` /\ `p3 <= N`) /\
              ((`p3 = 0` -> ((In t `1` N) -> (In t l3 u3)))) /\
              ((`p3 > 0` -> `(access t p3) = v`))) /\ `l3 > u3` l2 m1 
              p2 u2 result3 Post9) end) `2 + u0 - l0` l0 m p0 u0
        (refl_equal ? `2 + u0 - l0`)
        (binary_search_po_9 t Pre7 l0 Post1 u0 Post2 p0 Post3)) in
    (exist_5 [l2: Z][m1: Z][p2: Z][u2: Z][result3: unit](`1 <= p2` /\
    `p2 <= N`) /\ `(access t p2) = v` \/ `p2 = 0` /\ ~(In t `1` N) l1 
    m0 p1 u1 result2
    (binary_search_po_10 t Pre7 l0 Post1 u0 Post2 p0 Post3 l1 p1 u1 Post9)).

