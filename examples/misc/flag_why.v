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
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma dutch_flag_po_2 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  `0 <= i0` /\ `i0 < N`.
Proof.
Intuition.
Save.

Lemma dutch_flag_po_3 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
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
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test5: (access t0 i0) = blue)
  (Pre8: `0 <= b0` /\ `b0 < N`)
  (u: color)
  (Post9: u = (access t0 b0))
  `0 <= i0` /\ `i0 < N`.
Proof.
Intuition.
Save.

Lemma dutch_flag_po_5 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test5: (access t0 i0) = blue)
  (Pre8: `0 <= b0` /\ `b0 < N`)
  (u: color)
  (Post9: u = (access t0 b0))
  (Pre9: `0 <= i0` /\ `i0 < N`)
  (t1: (array N color))
  (Post10: t1 = (store t0 b0 (access t0 i0)))
  (t2: (array N color))
  (Post11: t2 = (store t1 i0 u))
  ((b:Z)
   (b = `b0 + 1` ->
    ((i:Z)
     (i = `i0 + 1` -> `0 <= b` /\ `b <= i` /\ (`i <= r0` /\ `r0 <= N`) /\
      (monochrome t2 `0` b blue) /\ (monochrome t2 b i white) /\
      (monochrome t2 r0 N red) /\ (Zwf `0` `r0 - i` `r0 - i0`))))).
Proof.
Unfold monochrome Zwf; Intuition Try Omega.
Assert h:`k < b0` \/ k=b0. Omega. Intuition.
Rewrite Post11; Rewrite store_def_2; Try Omega.
Rewrite Post10; Rewrite store_def_2; Try Omega.
Auto.
Assert h:`b0 = i0` \/ `b0 < i0`. Omega. Intuition.
Rewrite H12; Rewrite Post11; Rewrite H15.
Rewrite store_def_1.
Rewrite Post9; Rewrite H15; Assumption.
Omega.
Rewrite Post11; Rewrite store_def_2; Try Omega.
Rewrite Post10; Rewrite H12; Rewrite store_def_1; Try Omega.
Assumption.
Assert h:`k = i0` \/ `k < i0`. Omega. Intuition.
Rewrite Post11; Rewrite H12; Rewrite store_def_1; Try Omega.
Rewrite Post9; Apply H5; Omega.
Rewrite Post11; Rewrite store_def_2; Try Omega.
Rewrite Post10; Rewrite store_def_2; Try Omega.
Apply H5; Omega.
Rewrite Post11; Rewrite store_def_2; Try Omega.
Rewrite Post10; Rewrite store_def_2; Try Omega.
Apply H8; Omega.
Save.

Lemma dutch_flag_po_6 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test5: (access t0 i0) = blue)
  (t1: (array N color))
  (Post24: ((b:Z)
            (b = `b0 + 1` ->
             ((i:Z)
              (i = `i0 + 1` -> `0 <= b` /\ `b <= i` /\ (`i <= r0` /\
               `r0 <= N`) /\ (monochrome t1 `0` b blue) /\
               (monochrome t1 b i white) /\ (monochrome t1 r0 N red) /\
               (Zwf `0` `r0 - i` `r0 - i0`))))))
  (b1: Z)
  (Post12: b1 = `b0 + 1`)
  (i1: Z)
  (Post13: i1 = `i0 + 1`)
  `0 <= b1` /\ `b1 <= i1` /\ (`i1 <= r0` /\ `r0 <= N`) /\
  (monochrome t1 `0` b1 blue) /\ (monochrome t1 b1 i1 white) /\
  (monochrome t1 r0 N red) /\ (Zwf `0` `r0 - i1` `r0 - i0`).
Proof.
Intuition.
Save.

Lemma dutch_flag_po_7 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
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
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test4: ~((access t0 i0) = blue))
  (Test3: (access t0 i0) = white)
  (i1: Z)
  (Post8: i1 = `i0 + 1`)
  `0 <= b0` /\ `b0 <= i1` /\ (`i1 <= r0` /\ `r0 <= N`) /\
  (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i1 white) /\
  (monochrome t0 r0 N red) /\ (Zwf `0` `r0 - i1` `r0 - i0`).
Proof.
Unfold monochrome Zwf; Intuition Try Omega.
Assert h:`k<i0` \/ k=i0. Omega. Intuition.
Rewrite H5; Assumption.
Save.

Lemma dutch_flag_po_9 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test4: ~((access t0 i0) = blue))
  (Test2: ~((access t0 i0) = white))
  (r1: Z)
  (Post4: r1 = `r0 - 1`)
  `0 <= r1` /\ `r1 < N`.
Proof.
Intuition.
Save.

Lemma dutch_flag_po_10 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test4: ~((access t0 i0) = blue))
  (Test2: ~((access t0 i0) = white))
  (r1: Z)
  (Post4: r1 = `r0 - 1`)
  (Pre4: `0 <= r1` /\ `r1 < N`)
  (u: color)
  (Post5: u = (access t0 r1))
  `0 <= i0` /\ `i0 < N`.
Proof.
Intuition.
Save.

Lemma dutch_flag_po_11 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (Test4: ~((access t0 i0) = blue))
  (Test2: ~((access t0 i0) = white))
  (r1: Z)
  (Post4: r1 = `r0 - 1`)
  (Pre4: `0 <= r1` /\ `r1 < N`)
  (u: color)
  (Post5: u = (access t0 r1))
  (Pre5: `0 <= i0` /\ `i0 < N`)
  (t1: (array N color))
  (Post6: t1 = (store t0 r1 (access t0 i0)))
  (t2: (array N color))
  (Post7: t2 = (store t1 i0 u))
  `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r1` /\ `r1 <= N`) /\
  (monochrome t2 `0` b0 blue) /\ (monochrome t2 b0 i0 white) /\
  (monochrome t2 r1 N red) /\ (Zwf `0` `r1 - i0` `r0 - i0`).
Proof.
Unfold monochrome Zwf; Intuition Try Omega.
Rewrite Post7; Rewrite store_def_2; Try Omega.
Rewrite Post6; Rewrite store_def_2; Try Omega.
Apply H0; Omega.
Rewrite Post7; Rewrite store_def_2; Try Omega.
Rewrite Post6; Rewrite store_def_2; Try Omega.
Apply H3; Omega.
Assert h:`k = r1` \/ `r1 < k`. Omega. Intuition.
Assert h':`k = i0` \/ `i0 < k`. Omega. Intuition.
Rewrite Post7; Rewrite H13; Rewrite store_def_1.
Rewrite Post5; Rewrite <- H10; Rewrite H13.
Generalize Test4; Generalize Test2 ; Case (access t0 i0); Tauto.
Omega.
Rewrite Post7; Rewrite store_def_2; Try Omega.
Rewrite Post6; Rewrite H10; Rewrite store_def_1; Try Omega.
Generalize Test4; Generalize Test2 ; Case (access t0 i0); Tauto.
Rewrite Post7; Rewrite store_def_2; Try Omega.
Rewrite Post6; Rewrite store_def_2; Try Omega.
Apply H6; Omega.
Save.

Lemma dutch_flag_po_12 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (b1: Z)
  (i1: Z)
  (r1: Z)
  (t1: (array N color))
  (Post15: `0 <= b1` /\ `b1 <= i1` /\ (`i1 <= r1` /\ `r1 <= N`) /\
           (monochrome t1 `0` b1 blue) /\ (monochrome t1 b1 i1 white) /\
           (monochrome t1 r1 N red) /\ (Zwf `0` `r1 - i1` `r0 - i0`))
  (Zwf `0` `r1 - i1` Variant1).
Proof.
Intros; Rewrite Pre13; Tauto.
Save.

Lemma dutch_flag_po_13 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test6: `i0 < r0`)
  (b1: Z)
  (i1: Z)
  (r1: Z)
  (t1: (array N color))
  (Post15: `0 <= b1` /\ `b1 <= i1` /\ (`i1 <= r1` /\ `r1 <= N`) /\
           (monochrome t1 `0` b1 blue) /\ (monochrome t1 b1 i1 white) /\
           (monochrome t1 r1 N red) /\ (Zwf `0` `r1 - i1` `r0 - i0`))
  `0 <= b1` /\ `b1 <= i1` /\ (`i1 <= r1` /\ `r1 <= N`) /\
  (monochrome t1 `0` b1 blue) /\ (monochrome t1 b1 i1 white) /\
  (monochrome t1 r1 N red).
Proof.
Intuition.
Save.

Lemma dutch_flag_po_14 : 
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  (Variant1: Z)
  (b0: Z)
  (i0: Z)
  (r0: Z)
  (t0: (array N color))
  (Pre13: Variant1 = `r0 - i0`)
  (Pre12: `0 <= b0` /\ `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
          (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
          (monochrome t0 r0 N red))
  (Test1: `i0 >= r0`)
  (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 r0 white) /\
  (monochrome t0 r0 N red).
Proof.
Unfold monochrome; Intuition.
Save.

Lemma dutch_flag_po_15 : 
  (t: (array N color))
  (result: Z)
  (Post1: result = `0`)
  (result0: Z)
  (Post2: result0 = `0`)
  (result1: Z)
  (Post3: result1 = N)
  `0 <= result` /\ `result <= result0` /\ (`result0 <= result1` /\
  `result1 <= N`) /\ (monochrome t `0` result blue) /\
  (monochrome t result result0 white) /\ (monochrome t result1 N red).
Proof.
Intuition 
  (Try Rewrite Post1; Try Rewrite Post2; Try Rewrite Post3;
  Try Omega).
Exact N_non_negative.
Unfold monochrome; Intros; Absurd `0<0`; Omega.
Unfold monochrome; Intros; Absurd `0<0`; Omega.
Unfold monochrome; Intros; Absurd `N<N`; Omega.
Save.

Definition dutch_flag := (* validation *)
  [t: (array N color)]
    let (result, Post1) = (exist_1 [result: Z]result = `0` `0`
      (refl_equal ? `0`)) in
    let (b0, t0, result0) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = `0` `0`
        (refl_equal ? `0`)) in
      let (b0, i0, t0, result1) =
        let (result1, Post3) = (exist_1 [result1: Z]result1 = N N
          (refl_equal ? N)) in
        let (b0, i0, r0, t0, result2, Post18) =
          (well_founded_induction Z (Zwf ZERO)
            (dutch_flag_po_1 result Post1 result0 Post2 result1 Post3)
            [Variant1: Z](b0: Z)(i0: Z)(r0: Z)(t0: (array N color))
            (_: Variant1 = `r0 - i0`)(_0: `0 <= b0` /\ `b0 <= i0` /\
            (`i0 <= r0` /\ `r0 <= N`) /\ (monochrome t0 `0` b0 blue) /\
            (monochrome t0 b0 i0 white) /\ (monochrome t0 r0 N red))
            (sig_5 Z Z Z (array N color) unit [b1: Z][i1: Z][r1: Z]
             [t1: (array N color)][result2: unit]
             ((monochrome t1 `0` b1 blue) /\ (monochrome t1 b1 r1 white) /\
             (monochrome t1 r1 N red)))
            [Variant1: Z; wf1: (Variant2: Z)
             (Pre1: (Zwf `0` Variant2 Variant1))(b0: Z)(i0: Z)(r0: Z)
             (t0: (array N color))(_: Variant2 = `r0 - i0`)(_0: `0 <= b0` /\
             `b0 <= i0` /\ (`i0 <= r0` /\ `r0 <= N`) /\
             (monochrome t0 `0` b0 blue) /\ (monochrome t0 b0 i0 white) /\
             (monochrome t0 r0 N red))
             (sig_5 Z Z Z (array N color) unit [b1: Z][i1: Z][r1: Z]
              [t1: (array N color)][result2: unit]
              ((monochrome t1 `0` b1 blue) /\ (monochrome t1 b1 r1 white) /\
              (monochrome t1 r1 N red)));
             b0: Z; i0: Z; r0: Z; t0: (array N color);
             Pre13: Variant1 = `r0 - i0`; Pre12: `0 <= b0` /\ `b0 <= i0` /\
             (`i0 <= r0` /\ `r0 <= N`) /\ (monochrome t0 `0` b0 blue) /\
             (monochrome t0 b0 i0 white) /\ (monochrome t0 r0 N red)]
              let (result2, Bool1) =
                let (result4, Post19) = (Z_lt_ge_bool i0 r0) in
                (exist_1 [result5: bool]
                (if result5 then `i0 < r0` else `i0 >= r0`) result4 Post19) in
              (Cases (btest
                      [result2:bool](if result2 then `i0 < r0`
                                     else `i0 >= r0`)
                      result2 Bool1) of
              | (left Test6) =>
                  let (b1, i1, r1, t1, result3, Post21) =
                    let (b1, i1, r1, t1, result3, Post15) =
                      let (b1, i1, r1, t1, result3, Post15) =
                        let (result3, Bool3) =
                          let Pre2 =
                            (dutch_flag_po_2 result Post1 result0 Post2
                            result1 Post3 Variant1 b0 i0 r0 t0 Pre13 Pre12
                            Test6) in
                          let (result5, Post22) = (eq_blue (access t0 i0)) in
                          (exist_1 [result6: bool]
                          (if result6 then (access t0 i0) = blue
                           else ~((access t0 i0) = blue)) result5
                          Post22) in
                        (Cases (btest
                                [result3:bool](if result3
                                               then (access t0 i0) = blue
                                               else ~((access t0 i0) = blue))
                                result3 Bool3) of
                        | (left Test5) =>
                            let (b1, i1, t1, result4, Post15) =
                              let (t1, result4, Post24) =
                                let Pre8 =
                                  (dutch_flag_po_3 result Post1 result0 Post2
                                  result1 Post3 Variant1 b0 i0 r0 t0 Pre13
                                  Pre12 Test6 Test5) in
                                let (u, Post9) = (exist_1 [result4: color]
                                  result4 = (access t0 b0) (access t0 b0)
                                  (refl_equal ? (access t0 b0))) in
                                let (t1, result4, Post25) =
                                  let Pre9 =
                                    (dutch_flag_po_4 result Post1 result0
                                    Post2 result1 Post3 Variant1 b0 i0 r0 t0
                                    Pre13 Pre12 Test6 Test5 Pre8 u Post9) in
                                  let (t1, result4, Post10) =
                                    let (result4, Post10) =
                                      (exist_1 [result4: color]
                                      (store t0 b0 result4) =
                                      (store t0 b0 (access t0 i0)) (access t0
                                                                    i0)
                                      (refl_equal ? (store t0 b0
                                                     (access t0 i0)))) in
                                    let Pre10 = Pre8 in
                                    (exist_2 [t2: (array N color)]
                                    [result6: unit]
                                    t2 = (store t0 b0 (access t0 i0)) 
                                    (store t0 b0 result4) tt Post10) in
                                  let (t2, result5, Post11) =
                                    let (result5, Post11) =
                                      (exist_1 [result5: color]
                                      (store t1 i0 result5) = (store t1 i0 u) 
                                      u (refl_equal ? (store t1 i0 u))) in
                                    let Pre11 = Pre9 in
                                    (exist_2 [t3: (array N color)]
                                    [result7: unit]
                                    t3 = (store t1 i0 u) (store t1 i0 result5)
                                    tt Post11) in
                                  (exist_2 [t3: (array N color)]
                                  [result6: unit]
                                  ((b:Z)
                                   (b = `b0 + 1` ->
                                    ((i:Z)
                                     (i = `i0 + 1` -> `0 <= b` /\ `b <= i` /\
                                      (`i <= r0` /\ `r0 <= N`) /\
                                      (monochrome t3 `0` b blue) /\
                                      (monochrome t3 b i white) /\
                                      (monochrome t3 r0 N red) /\
                                      (Zwf `0` `r0 - i` `r0 - i0`))))) 
                                  t2 result5
                                  (dutch_flag_po_5 result Post1 result0 Post2
                                  result1 Post3 Variant1 b0 i0 r0 t0 Pre13
                                  Pre12 Test6 Test5 Pre8 u Post9 Pre9 t1
                                  Post10 t2 Post11)) in
                                (exist_2 [t2: (array N color)][result5: unit]
                                ((b:Z)
                                 (b = `b0 + 1` ->
                                  ((i:Z)
                                   (i = `i0 + 1` -> `0 <= b` /\ `b <= i` /\
                                    (`i <= r0` /\ `r0 <= N`) /\
                                    (monochrome t2 `0` b blue) /\
                                    (monochrome t2 b i white) /\
                                    (monochrome t2 r0 N red) /\
                                    (Zwf `0` `r0 - i` `r0 - i0`))))) 
                                t1 result4 Post25) in
                              let (b1, result5, Post12) =
                                let (result5, Post12) = (exist_1 [result5: Z]
                                  result5 = `b0 + 1` `b0 + 1`
                                  (refl_equal ? `b0 + 1`)) in
                                (exist_2 [b2: Z][result6: unit]
                                b2 = `b0 + 1` result5 tt Post12) in
                              let (i1, result6, Post13) =
                                let (result6, Post13) = (exist_1 [result6: Z]
                                  result6 = `i0 + 1` `i0 + 1`
                                  (refl_equal ? `i0 + 1`)) in
                                (exist_2 [i2: Z][result7: unit]
                                i2 = `i0 + 1` result6 tt Post13) in
                              (exist_4 [b2: Z][i2: Z][t2: (array N color)]
                              [result7: unit]`0 <= b2` /\ `b2 <= i2` /\
                              (`i2 <= r0` /\ `r0 <= N`) /\
                              (monochrome t2 `0` b2 blue) /\
                              (monochrome t2 b2 i2 white) /\
                              (monochrome t2 r0 N red) /\
                              (Zwf `0` `r0 - i2` `r0 - i0`) b1 i1 t1 
                              result6
                              (dutch_flag_po_6 result Post1 result0 Post2
                              result1 Post3 Variant1 b0 i0 r0 t0 Pre13 Pre12
                              Test6 Test5 t1 Post24 b1 Post12 i1 Post13)) in
                            (exist_5 [b2: Z][i2: Z][r1: Z]
                            [t2: (array N color)][result5: unit]`0 <= b2` /\
                            `b2 <= i2` /\ (`i2 <= r1` /\ `r1 <= N`) /\
                            (monochrome t2 `0` b2 blue) /\
                            (monochrome t2 b2 i2 white) /\
                            (monochrome t2 r1 N red) /\
                            (Zwf `0` `r1 - i2` `r0 - i0`) b1 i1 r0 t1 
                            result4 Post15)
                        | (right Test4) =>
                            let (i1, r1, t1, result4, Post15) =
                              let (result4, Bool2) =
                                let Pre3 =
                                  (dutch_flag_po_7 result Post1 result0 Post2
                                  result1 Post3 Variant1 b0 i0 r0 t0 Pre13
                                  Pre12 Test6 Test4) in
                                let (result6, Post23) =
                                  (eq_white (access t0 i0)) in
                                (exist_1 [result7: bool]
                                (if result7 then (access t0 i0) = white
                                 else ~((access t0 i0) = white)) result6
                                Post23) in
                              (Cases (btest
                                      [result4:bool](if result4
                                                     then (access t0 i0) =
                                                          white
                                                     else ~((access t0 i0) =
                                                     white))
                                      result4 Bool2) of
                              | (left Test3) =>
                                  let (i1, result5, Post8) =
                                    let (result5, Post8) =
                                      (exist_1 [result5: Z]
                                      result5 = `i0 + 1` `i0 + 1`
                                      (refl_equal ? `i0 + 1`)) in
                                    (exist_2 [i2: Z][result6: unit]
                                    i2 = `i0 + 1` result5 tt Post8) in
                                  (exist_4 [i2: Z][r1: Z]
                                  [t1: (array N color)][result6: unit]
                                  `0 <= b0` /\ `b0 <= i2` /\ (`i2 <= r1` /\
                                  `r1 <= N`) /\
                                  (monochrome t1 `0` b0 blue) /\
                                  (monochrome t1 b0 i2 white) /\
                                  (monochrome t1 r1 N red) /\
                                  (Zwf `0` `r1 - i2` `r0 - i0`) i1 r0 
                                  t0 result5
                                  (dutch_flag_po_8 result Post1 result0 Post2
                                  result1 Post3 Variant1 b0 i0 r0 t0 Pre13
                                  Pre12 Test6 Test4 Test3 i1 Post8))
                              | (right Test2) =>
                                  let (r1, t1, result5, Post15) =
                                    let (r1, result5, Post4) =
                                      let (result5, Post4) =
                                        (exist_1 [result5: Z]
                                        result5 = `r0 - 1` `r0 - 1`
                                        (refl_equal ? `r0 - 1`)) in
                                      (exist_2 [r2: Z][result6: unit]
                                      r2 = `r0 - 1` result5 tt Post4) in
                                    let (t1, result6, Post15) =
                                      let Pre4 =
                                        (dutch_flag_po_9 result Post1 result0
                                        Post2 result1 Post3 Variant1 b0 i0 r0
                                        t0 Pre13 Pre12 Test6 Test4 Test2 r1
                                        Post4) in
                                      let (u, Post5) =
                                        (exist_1 [result6: color]
                                        result6 = (access t0 r1) (access t0
                                                                  r1)
                                        (refl_equal ? (access t0 r1))) in
                                      let (t1, result6, Post15) =
                                        let Pre5 =
                                          (dutch_flag_po_10 result Post1
                                          result0 Post2 result1 Post3
                                          Variant1 b0 i0 r0 t0 Pre13 Pre12
                                          Test6 Test4 Test2 r1 Post4 Pre4 u
                                          Post5) in
                                        let (t1, result6, Post6) =
                                          let (result6, Post6) =
                                            (exist_1 [result6: color]
                                            (store t0 r1 result6) =
                                            (store t0 r1 (access t0 i0)) 
                                            (access t0 i0)
                                            (refl_equal ? (store t0 r1
                                                           (access t0 i0)))) in
                                          let Pre6 = Pre4 in
                                          (exist_2 [t2: (array N color)]
                                          [result8: unit]
                                          t2 = (store t0 r1 (access t0 i0)) 
                                          (store t0 r1 result6) tt Post6) in
                                        let (t2, result7, Post7) =
                                          let (result7, Post7) =
                                            (exist_1 [result7: color]
                                            (store t1 i0 result7) =
                                            (store t1 i0 u) u
                                            (refl_equal ? (store t1 i0 u))) in
                                          let Pre7 = Pre5 in
                                          (exist_2 [t3: (array N color)]
                                          [result9: unit]
                                          t3 = (store t1 i0 u) (store t1 i0
                                                                result7)
                                          tt Post7) in
                                        (exist_2 [t3: (array N color)]
                                        [result8: unit]`0 <= b0` /\
                                        `b0 <= i0` /\ (`i0 <= r1` /\
                                        `r1 <= N`) /\
                                        (monochrome t3 `0` b0 blue) /\
                                        (monochrome t3 b0 i0 white) /\
                                        (monochrome t3 r1 N red) /\
                                        (Zwf `0` `r1 - i0` `r0 - i0`) 
                                        t2 result7
                                        (dutch_flag_po_11 result Post1
                                        result0 Post2 result1 Post3 Variant1
                                        b0 i0 r0 t0 Pre13 Pre12 Test6 Test4
                                        Test2 r1 Post4 Pre4 u Post5 Pre5 t1
                                        Post6 t2 Post7)) in
                                      (exist_2 [t2: (array N color)]
                                      [result7: unit]`0 <= b0` /\
                                      `b0 <= i0` /\ (`i0 <= r1` /\
                                      `r1 <= N`) /\
                                      (monochrome t2 `0` b0 blue) /\
                                      (monochrome t2 b0 i0 white) /\
                                      (monochrome t2 r1 N red) /\
                                      (Zwf `0` `r1 - i0` `r0 - i0`) t1
                                      result6 Post15) in
                                    (exist_3 [r2: Z][t2: (array N color)]
                                    [result7: unit]`0 <= b0` /\ `b0 <= i0` /\
                                    (`i0 <= r2` /\ `r2 <= N`) /\
                                    (monochrome t2 `0` b0 blue) /\
                                    (monochrome t2 b0 i0 white) /\
                                    (monochrome t2 r2 N red) /\
                                    (Zwf `0` `r2 - i0` `r0 - i0`) r1 
                                    t1 result6 Post15) in
                                  (exist_4 [i1: Z][r2: Z]
                                  [t2: (array N color)][result6: unit]
                                  `0 <= b0` /\ `b0 <= i1` /\ (`i1 <= r2` /\
                                  `r2 <= N`) /\
                                  (monochrome t2 `0` b0 blue) /\
                                  (monochrome t2 b0 i1 white) /\
                                  (monochrome t2 r2 N red) /\
                                  (Zwf `0` `r2 - i1` `r0 - i0`) i0 r1 
                                  t1 result5 Post15) end) in
                            (exist_5 [b1: Z][i2: Z][r2: Z]
                            [t2: (array N color)][result5: unit]`0 <= b1` /\
                            `b1 <= i2` /\ (`i2 <= r2` /\ `r2 <= N`) /\
                            (monochrome t2 `0` b1 blue) /\
                            (monochrome t2 b1 i2 white) /\
                            (monochrome t2 r2 N red) /\
                            (Zwf `0` `r2 - i2` `r0 - i0`) b0 i1 r1 t1 
                            result4 Post15) end) in
                      (exist_5 [b2: Z][i2: Z][r2: Z][t2: (array N color)]
                      [result4: unit]`0 <= b2` /\ `b2 <= i2` /\
                      (`i2 <= r2` /\ `r2 <= N`) /\
                      (monochrome t2 `0` b2 blue) /\
                      (monochrome t2 b2 i2 white) /\
                      (monochrome t2 r2 N red) /\
                      (Zwf `0` `r2 - i2` `r0 - i0`) b1 i1 r1 t1 result3
                      Post15) in
                    ((wf1 `r1 - i1`)
                      (dutch_flag_po_12 result Post1 result0 Post2 result1
                      Post3 Variant1 b0 i0 r0 t0 Pre13 Pre12 Test6 b1 i1 r1
                      t1 Post15) b1 i1 r1 t1 (refl_equal ? `r1 - i1`)
                      (dutch_flag_po_13 result Post1 result0 Post2 result1
                      Post3 Variant1 b0 i0 r0 t0 Pre13 Pre12 Test6 b1 i1 r1
                      t1 Post15)) in
                  (exist_5 [b2: Z][i2: Z][r2: Z][t2: (array N color)]
                  [result4: unit](monochrome t2 `0` b2 blue) /\
                  (monochrome t2 b2 r2 white) /\ (monochrome t2 r2 N red) 
                  b1 i1 r1 t1 result3 Post21)
              | (right Test1) =>
                  let (b1, i1, r1, t1, result3, Post20) = (exist_5 [b1: Z]
                    [i1: Z][r1: Z][t1: (array N color)][result3: unit]
                    (monochrome t1 `0` b1 blue) /\
                    (monochrome t1 b1 r1 white) /\
                    (monochrome t1 r1 N red) b0 i0 r0 t0 tt
                    (dutch_flag_po_14 result Post1 result0 Post2 result1
                    Post3 Variant1 b0 i0 r0 t0 Pre13 Pre12 Test1)) in
                  (exist_5 [b2: Z][i2: Z][r2: Z][t2: (array N color)]
                  [result4: unit](monochrome t2 `0` b2 blue) /\
                  (monochrome t2 b2 r2 white) /\ (monochrome t2 r2 N red) 
                  b1 i1 r1 t1 result3 Post20) end) `result1 - result0` 
            result result0 result1 t (refl_equal ? `result1 - result0`)
            (dutch_flag_po_15 t result Post1 result0 Post2 result1 Post3)) in
        (Build_tuple_4 b0 i0 t0 result2) in
      (Build_tuple_3 b0 t0 result1) in
    (Build_tuple_2 t0 result0).

