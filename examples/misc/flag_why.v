(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Sumbool.

(*Why*) Parameter N : Z.

Axiom N_non_negative : `0 <= N`.

Inductive color : Set := blue : color | white : color | red : color.

Lemma eq_color_dec : (c1,c2:color) { c1=c2 } + { ~c1=c2 }.
Proof. 
Intros; Decide Equality c1 c2.
Save.

Definition eq_blue :=  [c](bool_of_sumbool (eq_color_dec c blue)).
Definition eq_white := [c](bool_of_sumbool (eq_color_dec c white)).

Definition monochrome [t:(array N color); i,j:Z; c:color] : Prop :=
  (k:Z)`i <= k < j` -> #t[k]=c.

Lemma dutch_flag_po_1 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (well_founded (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma dutch_flag_po_2 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: (`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  `0 <= i0` /\ `i0 < N`.
Proof.
Intuition.
Save.

Lemma dutch_flag_po_3 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: (`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test5: (access t0 i0) = blue)
  `0 <= b0` /\ `b0 < N`.
Proof.
Intuition.
Save.

Lemma dutch_flag_po_4 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: (`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test5: (access t0 i0) = blue)
  (Pre8: `0 <= b0` /\ `b0 < N`)
  (u: color)
  (Post3: u = (access t0 b0))
  `0 <= i0` /\ `i0 < N`.
Proof.
Intuition.
Save.

Lemma dutch_flag_po_5 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: (`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test5: (access t0 i0) = blue)
  (Pre8: `0 <= b0` /\ `b0 < N`)
  (u: color)
  (Post3: u = (access t0 b0))
  (Pre9: `0 <= i0` /\ `i0 < N`)
  (t1: (array N color))
  (Post1: t1 = (store t0 b0 (access t0 i0)))
  (t2: (array N color))
  (Post2: t2 = (store t1 i0 u))
  ((b:Z)
   (b = `b0 + 1` ->
    ((i:Z)
     (i = `i0 + 1` -> ((`0 <= b` /\ `b <= i`) /\ (`i <= r0` /\ `r0 <= N`) /\
      (monochrome t2 `0` b blue) /\ (monochrome t2 b i white) /\
      (monochrome t2 r0 N red)) /\ (Zwf `0` `r0 - i` `r0 - i0`))))).
Proof.
Unfold monochrome Zwf; Intuition Try Omega.
Assert h:`k < b0` \/ k=b0. Omega. Intuition.
Subst t2; Rewrite store_def_2; Try Omega.
Subst t1; Rewrite store_def_2; Try Omega.
Auto.
Assert h:`b0 = i0` \/ `b0 < i0`. Omega. Intuition.
Subst k t2 b0.
Rewrite store_def_1.
Subst u; Assumption.
Omega.
Subst t2; Rewrite store_def_2; Try Omega.
Subst t1 k; Rewrite store_def_1; Try Omega.
Assumption.
Assert h:`k = i0` \/ `k < i0`. Omega. Intuition.
Subst t2 k; Rewrite store_def_1; Try Omega.
Subst u; Apply H5; Omega.
Subst t2; Rewrite store_def_2; Try Omega.
Subst t1; Rewrite store_def_2; Try Omega.
Apply H5; Omega.
Subst t2; Rewrite store_def_2; Try Omega.
Subst t1; Rewrite store_def_2; Try Omega.
Apply H8; Omega.
Save.

Lemma dutch_flag_po_6 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: (`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test5: (access t0 i0) = blue)
  (t1: (array N color))
  (Post23: ((b:Z)
            (b = `b0 + 1` ->
             ((i:Z)
              (i = `i0 + 1` -> ((`0 <= b` /\ `b <= i`) /\ (`i <= r0` /\
               `r0 <= N`) /\ (monochrome t1 `0` b blue) /\
               (monochrome t1 b i white) /\ (monochrome t1 r0 N red)) /\
               (Zwf `0` `r0 - i` `r0 - i0`))))))
  (b1: Z)
  (Post4: b1 = `b0 + 1`)
  (i1: Z)
  (Post5: i1 = `i0 + 1`)
  ((`0 <= b1` /\ `b1 <= i1`) /\ (`i1 <= r0` /\ `r0 <= N`) /\
  (monochrome t1 `0` b1 blue) /\ (monochrome t1 b1 i1 white) /\
  (monochrome t1 r0 N red)) /\ (Zwf `0` `r0 - i1` `r0 - i0`).
Proof.
Intuition.
Save.

Lemma dutch_flag_po_7 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: (`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test4: ~((access t0 i0) = blue))
  `0 <= i0` /\ `i0 < N`.
Proof.
Intuition.
Save.

Lemma dutch_flag_po_8 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: (`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test4: ~((access t0 i0) = blue))
  (Test3: (access t0 i0) = white)
  (i1: Z)
  (Post6: i1 = `i0 + 1`)
  ((`0 <= b0` /\ `b0 <= i1`) /\ (`i1 <= r0` /\ `r0 <= N`) /\
  (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i1 white) /\
  (monochrome t0 r0 N red)) /\ (Zwf `0` `r0 - i1` `r0 - i0`).
Proof.
Unfold monochrome Zwf; Intuition Try Omega.
Assert h:`k<i0` \/ k=i0. Omega. Intuition.
Rewrite H5; Assumption.
Save.

Lemma dutch_flag_po_9 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: (`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test4: ~((access t0 i0) = blue))
  (Test2: ~((access t0 i0) = white))
  (r1: Z)
  (Post7: r1 = `r0 - 1`)
  `0 <= r1` /\ `r1 < N`.
Proof.
Intuition.
Save.

Lemma dutch_flag_po_10 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: (`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test4: ~((access t0 i0) = blue))
  (Test2: ~((access t0 i0) = white))
  (r1: Z)
  (Post7: r1 = `r0 - 1`)
  (Pre4: `0 <= r1` /\ `r1 < N`)
  (u: color)
  (Post10: u = (access t0 r1))
  `0 <= i0` /\ `i0 < N`.
Proof.
Intuition.
Save.

Lemma dutch_flag_po_11 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: (`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test4: ~((access t0 i0) = blue))
  (Test2: ~((access t0 i0) = white))
  (r1: Z)
  (Post7: r1 = `r0 - 1`)
  (Pre4: `0 <= r1` /\ `r1 < N`)
  (u: color)
  (Post10: u = (access t0 r1))
  (Pre5: `0 <= i0` /\ `i0 < N`)
  (t1: (array N color))
  (Post8: t1 = (store t0 r1 (access t0 i0)))
  (t2: (array N color))
  (Post9: t2 = (store t1 i0 u))
  ((`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r1` /\ `r1 <= N`) /\
  (monochrome t2 `0` b0 blue) /\ (monochrome t2 b0 i0 white) /\
  (monochrome t2 r1 N red)) /\ (Zwf `0` `r1 - i0` `r0 - i0`).
Proof.
Unfold monochrome Zwf; Intuition Try Omega.
Subst t2; Rewrite store_def_2; Try Omega.
Subst t1; Rewrite store_def_2; Try Omega.
Apply H; Omega.
Subst t2; Rewrite store_def_2; Try Omega.
Subst t1; Rewrite store_def_2; Try Omega.
Apply H3; Omega.
Assert h:`k = r1` \/ `r1 < k`. Omega. Intuition.
Assert h':`k = i0` \/ `i0 < k`. Omega. Intuition.
Subst t2 k; Rewrite store_def_1.
Subst u; Rewrite <- H10; Subst r1.
Generalize Test4; Generalize Test2 ; Case (access t0 i0); Tauto.
Omega.
Subst t2; Rewrite store_def_2; Try Omega.
Subst t1 k; Rewrite store_def_1; Try Omega.
Generalize Test4; Generalize Test2 ; Case (access t0 i0); Tauto.
Subst t2; Rewrite store_def_2; Try Omega.
Subst t1; Rewrite store_def_2; Try Omega.
Apply H6; Omega.
Save.

Lemma dutch_flag_po_12 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: (`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (b1: Z)
  (i1: Z)
  (r1: Z)
  (t1: (array N color))
  (Post14: ((`0 <= b1` /\ `b1 <= i1`) /\ (`i1 <= r1` /\ `r1 <= N`) /\
           (monochrome t1 `0` b1 blue) /\ (monochrome t1 b1 i1 white) /\
           (monochrome t1 r1 N red)) /\ (Zwf `0` `r1 - i1` `r0 - i0`))
  (Zwf `0` `r1 - i1` Variant1).
Proof.
Intros; Rewrite Pre13; Tauto.
Save.

Lemma dutch_flag_po_13 : 
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: (`0 <= b0` /\ `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test1: `i0 >= r0`)
  (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 r0 white) /\
  (monochrome t0 r0 N red).
Proof.
Unfold monochrome; Intuition.
Save.

Lemma dutch_flag_po_14 : 
  (t: (array N color))
  (result: Z)
  (Post13: result = `0`)
  (result0: Z)
  (Post12: result0 = `0`)
  (result1: Z)
  (Post11: result1 = N)
  (`0 <= result` /\ `result <= result0`) /\ (`result0 <= result1` /\
  `result1 <= N`) /\ (monochrome t `0` result blue) /\
  (monochrome t result result0 white) /\ (monochrome t result1 N red).
Proof.
Intuition
  (Try Subst result; Try Subst result0; Try Subst result1;
  Try Omega).
Exact N_non_negative.
Unfold monochrome; Intros; Absurd `0<0`; Omega.
Unfold monochrome; Intros; Absurd `0<0`; Omega.
Unfold monochrome; Intros; Absurd `N<N`; Omega.
Save.

Definition dutch_flag := (* validation *)
  [t: (array N color)]
    let (result, Post13) = (exist_1 [result: Z]result = `0` `0`
      (refl_equal ? `0`)) in
    let (b0, t0, result0) =
      let (result0, Post12) = (exist_1 [result0: Z]result0 = `0` `0`
        (refl_equal ? `0`)) in
      let (b0, i0, t0, result1) =
        let (result1, Post11) = (exist_1 [result1: Z]result1 = N N
          (refl_equal ? N)) in
        let (b0, i0, r0, t0, result2, Post17) =
          (well_founded_induction Z (Zwf ZERO)
            (dutch_flag_po_1 result Post13 result0 Post12 result1 Post11)
            [Variant1: Z](b0: Z)(i0: Z)(r0: Z)(t0: (array N color))
            (_: Variant1 = `r0 - i0`)(_0: (`0 <= b0` /\ `b0 <= i0`) /\
            (`i0 <= r0` /\ `r0 <= N`) /\ (monochrome t0 `0` b0 blue) /\
            (monochrome t0 b0 i0 white) /\ (monochrome t0 r0 N red))
            (sig_5 Z Z Z (array N color) unit [b1: Z][i1: Z][r1: Z]
             [t1: (array N color)][result2: unit]
             ((monochrome t1 `0` b1 blue) /\ (monochrome t1 b1 r1 white) /\
             (monochrome t1 r1 N red)))
            [Variant1: Z; wf1: (Variant2: Z)
             (Pre1: (Zwf `0` Variant2 Variant1))(b0: Z)(i0: Z)(r0: Z)
             (t0: (array N color))(_: Variant2 = `r0 - i0`)(_0: (`0 <= b0` /\
             `b0 <= i0`) /\ (`i0 <= r0` /\ `r0 <= N`) /\
             (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
             (monochrome t0 r0 N red))
             (sig_5 Z Z Z (array N color) unit [b1: Z][i1: Z][r1: Z]
              [t1: (array N color)][result2: unit]
              ((monochrome t1 `0` b1 blue) /\ (monochrome t1 b1 r1 white) /\
              (monochrome t1 r1 N red)));
             b0: Z; i0: Z; r0: Z; t0: (array N color);
             Pre13: Variant1 = `r0 - i0`; Pre12: (`0 <= b0` /\ `b0 <= i0`) /\
             (`i0 <= r0` /\ `r0 <= N`) /\ (monochrome t0 `0` b0 blue) /\
             (monochrome t0 b0 i0 white) /\ (monochrome t0 r0 N red)]
              let (result2, Bool3) =
                let (result4, Post18) = (Z_lt_ge_bool i0 r0) in
                (exist_1 [result5: bool]
                (if result5 then `i0 < r0` else `i0 >= r0`) result4 Post18) in
              (Cases (btest
                      [result2:bool](if result2 then `i0 < r0`
                                     else `i0 >= r0`)
                      result2 Bool3) of
              | (left Test6) =>
                  let (b1, i1, r1, t1, result3, Post20) =
                    let (b1, i1, r1, t1, result3, Post14) =
                      let (b1, i1, r1, t1, result3, Post14) =
                        let (result3, Bool2) =
                          let Pre2 =
                            (dutch_flag_po_2 result Post13 result0 Post12
                            result1 Post11 Variant1 b0 i0 r0 t0 Pre13 Pre12
                            Test6) in
                          let (result5, Post21) = (eq_blue (access t0 i0)) in
                          (exist_1 [result6: bool]
                          (if result6 then (access t0 i0) = blue
                           else ~((access t0 i0) = blue)) result5
                          Post21) in
                        (Cases (btest
                                [result3:bool](if result3
                                               then (access t0 i0) = blue
                                               else ~((access t0 i0) = blue))
                                result3 Bool2) of
                        | (left Test5) =>
                            let (b1, i1, t1, result4, Post14) =
                              let (t1, result4, Post23) =
                                let Pre8 =
                                  (dutch_flag_po_3 result Post13 result0
                                  Post12 result1 Post11 Variant1 b0 i0 r0 t0
                                  Pre13 Pre12 Test6 Test5) in
                                let (u, Post3) = (exist_1 [result4: color]
                                  result4 = (access t0 b0) (access t0 b0)
                                  (refl_equal ? (access t0 b0))) in
                                let (t1, result4, Post24) =
                                  let Pre9 =
                                    (dutch_flag_po_4 result Post13 result0
                                    Post12 result1 Post11 Variant1 b0 i0 r0
                                    t0 Pre13 Pre12 Test6 Test5 Pre8 u Post3) in
                                  let (t1, result4, Post1) =
                                    let (result4, Post1) =
                                      (exist_1 [result4: color]
                                      (store t0 b0 result4) = (store t0 b0
                                                               (access t0 i0)) 
                                      (access t0 i0)
                                      (refl_equal ? (store t0 b0
                                                     (access t0 i0)))) in
                                    let Pre10 = Pre8 in
                                    (exist_2 [t2: (array N color)]
                                    [result6: unit]
                                    t2 = (store t0 b0 (access t0 i0)) 
                                    (store t0 b0 result4) tt Post1) in
                                  let (t2, result5, Post2) =
                                    let (result5, Post2) =
                                      (exist_1 [result5: color]
                                      (store t1 i0 result5) = (store t1 i0 u) 
                                      u (refl_equal ? (store t1 i0 u))) in
                                    let Pre11 = Pre9 in
                                    (exist_2 [t3: (array N color)]
                                    [result7: unit]
                                    t3 = (store t1 i0 u) (store t1 i0 result5)
                                    tt Post2) in
                                  (exist_2 [t3: (array N color)]
                                  [result6: unit]
                                  ((b:Z)
                                   (b = `b0 + 1` ->
                                    ((i:Z)
                                     (i = `i0 + 1` -> ((`0 <= b` /\
                                      `b <= i`) /\ (`i <= r0` /\
                                      `r0 <= N`) /\
                                      (monochrome t3 `0` b blue) /\
                                      (monochrome t3 b i white) /\
                                      (monochrome t3 r0 N red)) /\
                                      (Zwf `0` `r0 - i` `r0 - i0`))))) 
                                  t2 result5
                                  (dutch_flag_po_5 result Post13 result0
                                  Post12 result1 Post11 Variant1 b0 i0 r0 t0
                                  Pre13 Pre12 Test6 Test5 Pre8 u Post3 Pre9
                                  t1 Post1 t2 Post2)) in
                                (exist_2 [t2: (array N color)][result5: unit]
                                ((b:Z)
                                 (b = `b0 + 1` ->
                                  ((i:Z)
                                   (i = `i0 + 1` -> ((`0 <= b` /\
                                    `b <= i`) /\ (`i <= r0` /\ `r0 <= N`) /\
                                    (monochrome t2 `0` b blue) /\
                                    (monochrome t2 b i white) /\
                                    (monochrome t2 r0 N red)) /\
                                    (Zwf `0` `r0 - i` `r0 - i0`))))) 
                                t1 result4 Post24) in
                              let (b1, result5, Post4) =
                                let (result5, Post4) = (exist_1 [result5: Z]
                                  result5 = `b0 + 1` `b0 + 1`
                                  (refl_equal ? `b0 + 1`)) in
                                (exist_2 [b2: Z][result6: unit]
                                b2 = `b0 + 1` result5 tt Post4) in
                              let (i1, result6, Post5) =
                                let (result6, Post5) = (exist_1 [result6: Z]
                                  result6 = `i0 + 1` `i0 + 1`
                                  (refl_equal ? `i0 + 1`)) in
                                (exist_2 [i2: Z][result7: unit]
                                i2 = `i0 + 1` result6 tt Post5) in
                              (exist_4 [b2: Z][i2: Z][t2: (array N color)]
                              [result7: unit]((`0 <= b2` /\ `b2 <= i2`) /\
                              (`i2 <= r0` /\ `r0 <= N`) /\
                              (monochrome t2 `0` b2 blue) /\
                              (monochrome t2 b2 i2 white) /\
                              (monochrome t2 r0 N red)) /\
                              (Zwf `0` `r0 - i2` `r0 - i0`) b1 i1 t1 
                              result6
                              (dutch_flag_po_6 result Post13 result0 Post12
                              result1 Post11 Variant1 b0 i0 r0 t0 Pre13 Pre12
                              Test6 Test5 t1 Post23 b1 Post4 i1 Post5)) in
                            (exist_5 [b2: Z][i2: Z][r1: Z]
                            [t2: (array N color)][result5: unit]
                            ((`0 <= b2` /\ `b2 <= i2`) /\ (`i2 <= r1` /\
                            `r1 <= N`) /\ (monochrome t2 `0` b2 blue) /\
                            (monochrome t2 b2 i2 white) /\
                            (monochrome t2 r1 N red)) /\
                            (Zwf `0` `r1 - i2` `r0 - i0`) b1 i1 r0 t1 
                            result4 Post14)
                        | (right Test4) =>
                            let (i1, r1, t1, result4, Post14) =
                              let (result4, Bool1) =
                                let Pre3 =
                                  (dutch_flag_po_7 result Post13 result0
                                  Post12 result1 Post11 Variant1 b0 i0 r0 t0
                                  Pre13 Pre12 Test6 Test4) in
                                let (result6, Post22) =
                                  (eq_white (access t0 i0)) in
                                (exist_1 [result7: bool]
                                (if result7 then (access t0 i0) = white
                                 else ~((access t0 i0) = white)) result6
                                Post22) in
                              (Cases (btest
                                      [result4:bool](if result4
                                                     then (access t0 i0) = white
                                                     else ~((access t0 i0) = white))
                                      result4 Bool1) of
                              | (left Test3) =>
                                  let (i1, result5, Post6) =
                                    let (result5, Post6) =
                                      (exist_1 [result5: Z]
                                      result5 = `i0 + 1` `i0 + 1`
                                      (refl_equal ? `i0 + 1`)) in
                                    (exist_2 [i2: Z][result6: unit]
                                    i2 = `i0 + 1` result5 tt Post6) in
                                  (exist_4 [i2: Z][r1: Z]
                                  [t1: (array N color)][result6: unit]
                                  ((`0 <= b0` /\ `b0 <= i2`) /\
                                  (`i2 <= r1` /\ `r1 <= N`) /\
                                  (monochrome t1 `0` b0 blue) /\
                                  (monochrome t1 b0 i2 white) /\
                                  (monochrome t1 r1 N red)) /\
                                  (Zwf `0` `r1 - i2` `r0 - i0`) i1 r0 
                                  t0 result5
                                  (dutch_flag_po_8 result Post13 result0
                                  Post12 result1 Post11 Variant1 b0 i0 r0 t0
                                  Pre13 Pre12 Test6 Test4 Test3 i1 Post6))
                              | (right Test2) =>
                                  let (r1, t1, result5, Post14) =
                                    let (r1, result5, Post7) =
                                      let (result5, Post7) =
                                        (exist_1 [result5: Z]
                                        result5 = `r0 - 1` `r0 - 1`
                                        (refl_equal ? `r0 - 1`)) in
                                      (exist_2 [r2: Z][result6: unit]
                                      r2 = `r0 - 1` result5 tt Post7) in
                                    let (t1, result6, Post14) =
                                      let Pre4 =
                                        (dutch_flag_po_9 result Post13
                                        result0 Post12 result1 Post11
                                        Variant1 b0 i0 r0 t0 Pre13 Pre12
                                        Test6 Test4 Test2 r1 Post7) in
                                      let (u, Post10) =
                                        (exist_1 [result6: color]
                                        result6 = (access t0 r1) (access t0
                                                                  r1)
                                        (refl_equal ? (access t0 r1))) in
                                      let (t1, result6, Post14) =
                                        let Pre5 =
                                          (dutch_flag_po_10 result Post13
                                          result0 Post12 result1 Post11
                                          Variant1 b0 i0 r0 t0 Pre13 Pre12
                                          Test6 Test4 Test2 r1 Post7 Pre4 u
                                          Post10) in
                                        let (t1, result6, Post8) =
                                          let (result6, Post8) =
                                            (exist_1 [result6: color]
                                            (store t0 r1 result6) = (
                                            store t0 r1 (access t0 i0)) 
                                            (access t0 i0)
                                            (refl_equal ? (store t0 r1
                                                           (access t0 i0)))) in
                                          let Pre6 = Pre4 in
                                          (exist_2 [t2: (array N color)]
                                          [result8: unit]
                                          t2 = (store t0 r1 (access t0 i0)) 
                                          (store t0 r1 result6) tt Post8) in
                                        let (t2, result7, Post9) =
                                          let (result7, Post9) =
                                            (exist_1 [result7: color]
                                            (store t1 i0 result7) = (
                                            store t1 i0 u) u
                                            (refl_equal ? (store t1 i0 u))) in
                                          let Pre7 = Pre5 in
                                          (exist_2 [t3: (array N color)]
                                          [result9: unit]
                                          t3 = (store t1 i0 u) (store t1 i0
                                                                result7)
                                          tt Post9) in
                                        (exist_2 [t3: (array N color)]
                                        [result8: unit]((`0 <= b0` /\
                                        `b0 <= i0`) /\ (`i0 <= r1` /\
                                        `r1 <= N`) /\
                                        (monochrome t3 `0` b0 blue) /\
                                        (monochrome t3 b0 i0 white) /\
                                        (monochrome t3 r1 N red)) /\
                                        (Zwf `0` `r1 - i0` `r0 - i0`) 
                                        t2 result7
                                        (dutch_flag_po_11 result Post13
                                        result0 Post12 result1 Post11
                                        Variant1 b0 i0 r0 t0 Pre13 Pre12
                                        Test6 Test4 Test2 r1 Post7 Pre4 u
                                        Post10 Pre5 t1 Post8 t2 Post9)) in
                                      (exist_2 [t2: (array N color)]
                                      [result7: unit]((`0 <= b0` /\
                                      `b0 <= i0`) /\ (`i0 <= r1` /\
                                      `r1 <= N`) /\
                                      (monochrome t2 `0` b0 blue) /\
                                      (monochrome t2 b0 i0 white) /\
                                      (monochrome t2 r1 N red)) /\
                                      (Zwf `0` `r1 - i0` `r0 - i0`) t1
                                      result6 Post14) in
                                    (exist_3 [r2: Z][t2: (array N color)]
                                    [result7: unit]((`0 <= b0` /\
                                    `b0 <= i0`) /\ (`i0 <= r2` /\
                                    `r2 <= N`) /\
                                    (monochrome t2 `0` b0 blue) /\
                                    (monochrome t2 b0 i0 white) /\
                                    (monochrome t2 r2 N red)) /\
                                    (Zwf `0` `r2 - i0` `r0 - i0`) r1 
                                    t1 result6 Post14) in
                                  (exist_4 [i1: Z][r2: Z]
                                  [t2: (array N color)][result6: unit]
                                  ((`0 <= b0` /\ `b0 <= i1`) /\
                                  (`i1 <= r2` /\ `r2 <= N`) /\
                                  (monochrome t2 `0` b0 blue) /\
                                  (monochrome t2 b0 i1 white) /\
                                  (monochrome t2 r2 N red)) /\
                                  (Zwf `0` `r2 - i1` `r0 - i0`) i0 r1 
                                  t1 result5 Post14) end) in
                            (exist_5 [b1: Z][i2: Z][r2: Z]
                            [t2: (array N color)][result5: unit]
                            ((`0 <= b1` /\ `b1 <= i2`) /\ (`i2 <= r2` /\
                            `r2 <= N`) /\ (monochrome t2 `0` b1 blue) /\
                            (monochrome t2 b1 i2 white) /\
                            (monochrome t2 r2 N red)) /\
                            (Zwf `0` `r2 - i2` `r0 - i0`) b0 i1 r1 t1 
                            result4 Post14) end) in
                      (exist_5 [b2: Z][i2: Z][r2: Z][t2: (array N color)]
                      [result4: unit]((`0 <= b2` /\ `b2 <= i2`) /\
                      (`i2 <= r2` /\ `r2 <= N`) /\
                      (monochrome t2 `0` b2 blue) /\
                      (monochrome t2 b2 i2 white) /\
                      (monochrome t2 r2 N red)) /\
                      (Zwf `0` `r2 - i2` `r0 - i0`) b1 i1 r1 t1 result3
                      Post14) in
                    ((wf1 `r1 - i1`)
                      (dutch_flag_po_12 result Post13 result0 Post12 result1
                      Post11 Variant1 b0 i0 r0 t0 Pre13 Pre12 Test6 b1 i1 r1
                      t1 Post14) b1 i1 r1 t1 (refl_equal ? `r1 - i1`)
                      (proj1 ? ? Post14)) in
                  (exist_5 [b2: Z][i2: Z][r2: Z][t2: (array N color)]
                  [result4: unit](monochrome t2 `0` b2 blue) /\
                  (monochrome t2 b2 r2 white) /\ (monochrome t2 r2 N red) 
                  b1 i1 r1 t1 result3 Post20)
              | (right Test1) =>
                  let (b1, i1, r1, t1, result3, Post19) = (exist_5 [b1: Z]
                    [i1: Z][r1: Z][t1: (array N color)][result3: unit]
                    (monochrome t1 `0` b1 blue) /\
                    (monochrome t1 b1 r1 white) /\
                    (monochrome t1 r1 N red) b0 i0 r0 t0 tt
                    (dutch_flag_po_13 result Post13 result0 Post12 result1
                    Post11 Variant1 b0 i0 r0 t0 Pre13 Pre12 Test1)) in
                  (exist_5 [b2: Z][i2: Z][r2: Z][t2: (array N color)]
                  [result4: unit](monochrome t2 `0` b2 blue) /\
                  (monochrome t2 b2 r2 white) /\ (monochrome t2 r2 N red) 
                  b1 i1 r1 t1 result3 Post19) end) `result1 - result0` 
            result result0 result1 t (refl_equal ? `result1 - result0`)
            (dutch_flag_po_14 t result Post13 result0 Post12 result1 Post11)) in
        (Build_tuple_4 b0 i0 t0 result2) in
      (Build_tuple_3 b0 t0 result1) in
    (Build_tuple_2 t0 result0).

