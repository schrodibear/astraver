(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

Parameter gcd : Z -> Z -> Z.

Axiom gcd_asubb_b : (a,b:Z) (gcd a b) = (gcd `a-b` b).
Axiom gcd_a_bsuba : (a,b:Z) (gcd a b) = (gcd a `b-a`).
Axiom gcd_a_a : (a:Z) (gcd a a) = a.
Axiom gcd_a_0 : (a:Z) (gcd a `0`) = a.
Axiom gcd_a_amodb : (a,b:Z) (gcd a b) = (gcd b (Zmod a b)).

Hints Resolve gcd_asubb_b gcd_a_bsuba gcd_a_a gcd_a_0 gcd_a_amodb.

Definition max : Z->Z->Z := 
  [x,y] Cases (Z_le_gt_dec x y) of (left _) => y | (right _) => x end.

Lemma gcd1_po_1 : 
  (a: Z)
  (b: Z)
  (Pre4: `a > 0` /\ `b > 0`)
  (result: Z)
  (Post1: result = a)
  (result0: Z)
  (Post2: result0 = b)
  (well_founded (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma gcd1_po_2 : 
  (a: Z)
  (b: Z)
  (Pre4: `a > 0` /\ `b > 0`)
  (result: Z)
  (Post1: result = a)
  (result0: Z)
  (Post2: result0 = b)
  (Variant1: Z)
  (x0: Z)
  (y0: Z)
  (Pre3: Variant1 = (max x0 y0))
  (Pre2: `0 < x0` /\ `0 < y0` /\ `(gcd x0 y0) = (gcd a b)`)
  (Test4: `x0 <> y0`)
  (Test3: `x0 > y0`)
  (x1: Z)
  (Post4: x1 = `x0 - y0`)
  (`0 < x1` /\ `0 < y0` /\ `(gcd x1 y0) = (gcd a b)`) /\
  (Zwf `0` (max x1 y0) (max x0 y0)).
Proof.
Intuition.
Rewrite Post4; Rewrite <- H4; Auto.
Unfold Zwf max.
Case (Z_le_gt_dec x1 y0); Case (Z_le_gt_dec x0 y0); Intros; Omega.
Save.

Lemma gcd1_po_3 : 
  (a: Z)
  (b: Z)
  (Pre4: `a > 0` /\ `b > 0`)
  (result: Z)
  (Post1: result = a)
  (result0: Z)
  (Post2: result0 = b)
  (Variant1: Z)
  (x0: Z)
  (y0: Z)
  (Pre3: Variant1 = (max x0 y0))
  (Pre2: `0 < x0` /\ `0 < y0` /\ `(gcd x0 y0) = (gcd a b)`)
  (Test4: `x0 <> y0`)
  (Test2: `x0 <= y0`)
  (y1: Z)
  (Post3: y1 = `y0 - x0`)
  (`0 < x0` /\ `0 < y1` /\ `(gcd x0 y1) = (gcd a b)`) /\
  (Zwf `0` (max x0 y1) (max x0 y0)).
Proof.
Intuition.
Assert h:~x0=y0. Assumption. Omega.
Rewrite Post3; Rewrite <- H4; Auto.
Unfold Zwf max.
Assert h:~x0=y0. Assumption. 
Case (Z_le_gt_dec x0 y1); Case (Z_le_gt_dec x0 y0); Intros; Omega.
Save.

Lemma gcd1_po_4 : 
  (a: Z)
  (b: Z)
  (Pre4: `a > 0` /\ `b > 0`)
  (result: Z)
  (Post1: result = a)
  (result0: Z)
  (Post2: result0 = b)
  (Variant1: Z)
  (x0: Z)
  (y0: Z)
  (Pre3: Variant1 = (max x0 y0))
  (Pre2: `0 < x0` /\ `0 < y0` /\ `(gcd x0 y0) = (gcd a b)`)
  (Test4: `x0 <> y0`)
  (x1: Z)
  (y1: Z)
  (Post6: (`0 < x1` /\ `0 < y1` /\ `(gcd x1 y1) = (gcd a b)`) /\
          (Zwf `0` (max x1 y1) (max x0 y0)))
  (Zwf `0` (max x1 y1) Variant1).
Proof.
Intuition.
Rewrite Pre3; Assumption.
Save.

Lemma gcd1_po_5 : 
  (a: Z)
  (b: Z)
  (Pre4: `a > 0` /\ `b > 0`)
  (result: Z)
  (Post1: result = a)
  (result0: Z)
  (Post2: result0 = b)
  `0 < result` /\ `0 < result0` /\ `(gcd result result0) = (gcd a b)`.
Proof.
Intuition.
Rewrite Post1; Rewrite Post2; Reflexivity.
Save.

Lemma gcd1_po_6 : 
  (a: Z)
  (b: Z)
  (Pre4: `a > 0` /\ `b > 0`)
  (result: Z)
  (Post1: result = a)
  (result0: Z)
  (Post2: result0 = b)
  (x0: Z)
  (y0: Z)
  (Post5: (`0 < x0` /\ `0 < y0` /\ `(gcd x0 y0) = (gcd a b)`) /\ `x0 = y0`)
  `x0 = (gcd a b)`.
Proof.
Intuition.
Rewrite <- H5; Rewrite H2.
Auto.
Save.

Definition gcd1 := (* validation *)
  [a: Z; b: Z; Pre4: `a > 0` /\ `b > 0`]
    let (result, Post1) = (exist_1 [result: Z]result = a a
      (refl_equal ? a)) in
    let (x0, result0, Post8) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = b b
        (refl_equal ? b)) in
      let (x0, y0, result1, Post9) =
        let (x0, y0, result1, Post5) =
          (well_founded_induction Z (Zwf ZERO)
            (gcd1_po_1 a b Pre4 result Post1 result0 Post2) [Variant1: Z]
            (x0: Z)(y0: Z)(_: Variant1 = (max x0 y0))(_0: `0 < x0` /\
            `0 < y0` /\ `(gcd x0 y0) = (gcd a b)`)
            (sig_3 Z Z unit [x1: Z][y1: Z][result1: unit]((`0 < x1` /\
             `0 < y1` /\ `(gcd x1 y1) = (gcd a b)`) /\ `x1 = y1`))
            [Variant1: Z; wf1: (Variant2: Z)
             (Pre1: (Zwf `0` Variant2 Variant1))(x0: Z)(y0: Z)
             (_: Variant2 = (max x0 y0))(_0: `0 < x0` /\ `0 < y0` /\
             `(gcd x0 y0) = (gcd a b)`)
             (sig_3 Z Z unit [x1: Z][y1: Z][result1: unit]((`0 < x1` /\
              `0 < y1` /\ `(gcd x1 y1) = (gcd a b)`) /\ `x1 = y1`));
             x0: Z; y0: Z; Pre3: Variant1 = (max x0 y0); Pre2: `0 < x0` /\
             `0 < y0` /\ `(gcd x0 y0) = (gcd a b)`]
              let (result1, Bool1) =
                let (result3, Post10) = (Z_noteq_bool x0 y0) in
                (exist_1 [result4: bool]
                (if result4 then `x0 <> y0` else `x0 = y0`) result3 Post10) in
              (Cases (btest
                      [result1:bool](if result1 then `x0 <> y0`
                                     else `x0 = y0`)
                      result1 Bool1) of
              | (left Test4) =>
                  let (x1, y1, result2, Post5) =
                    let (x1, y1, result2, Post6) =
                      let (x1, y1, result2, Post6) =
                        let (result2, Bool2) =
                          let (result4, Post11) = (Z_gt_le_bool x0 y0) in
                          (exist_1 [result5: bool]
                          (if result5 then `x0 > y0` else `x0 <= y0`) 
                          result4 Post11) in
                        (Cases (btest
                                [result2:bool](if result2 then `x0 > y0`
                                               else `x0 <= y0`)
                                result2 Bool2) of
                        | (left Test3) =>
                            let (x1, result3, Post4) =
                              let (result3, Post4) = (exist_1 [result3: Z]
                                result3 = `x0 - y0` `x0 - y0`
                                (refl_equal ? `x0 - y0`)) in
                              (exist_2 [x2: Z][result4: unit]
                              x2 = `x0 - y0` result3 tt Post4) in
                            (exist_3 [x2: Z][y1: Z][result4: unit]
                            (`0 < x2` /\ `0 < y1` /\
                            `(gcd x2 y1) = (gcd a b)`) /\
                            (Zwf `0` (max x2 y1) (max x0 y0)) x1 y0 result3
                            (gcd1_po_2 a b Pre4 result Post1 result0 Post2
                            Variant1 x0 y0 Pre3 Pre2 Test4 Test3 x1 Post4))
                        | (right Test2) =>
                            let (y1, result3, Post3) =
                              let (result3, Post3) = (exist_1 [result3: Z]
                                result3 = `y0 - x0` `y0 - x0`
                                (refl_equal ? `y0 - x0`)) in
                              (exist_2 [y2: Z][result4: unit]
                              y2 = `y0 - x0` result3 tt Post3) in
                            (exist_3 [x1: Z][y2: Z][result4: unit]
                            (`0 < x1` /\ `0 < y2` /\
                            `(gcd x1 y2) = (gcd a b)`) /\
                            (Zwf `0` (max x1 y2) (max x0 y0)) x0 y1 result3
                            (gcd1_po_3 a b Pre4 result Post1 result0 Post2
                            Variant1 x0 y0 Pre3 Pre2 Test4 Test2 y1 Post3)) end) in
                      (exist_3 [x2: Z][y2: Z][result3: unit](`0 < x2` /\
                      `0 < y2` /\ `(gcd x2 y2) = (gcd a b)`) /\
                      (Zwf `0` (max x2 y2) (max x0 y0)) x1 y1 result2 Post6) in
                    ((wf1 (max x1 y1))
                      (gcd1_po_4 a b Pre4 result Post1 result0 Post2 Variant1
                      x0 y0 Pre3 Pre2 Test4 x1 y1 Post6) x1 y1
                      (refl_equal ? (max x1 y1)) (proj1 ? ? Post6)) in
                  (exist_3 [x2: Z][y2: Z][result3: unit](`0 < x2` /\
                  `0 < y2` /\ `(gcd x2 y2) = (gcd a b)`) /\ `x2 = y2` 
                  x1 y1 result2 Post5)
              | (right Test1) =>
                  let (x1, y1, result2, Post5) = (exist_3 [x1: Z][y1: Z]
                    [result2: unit](`0 < x1` /\ `0 < y1` /\
                    `(gcd x1 y1) = (gcd a b)`) /\ `x1 = y1` x0 y0 tt
                    (conj ? ? Pre2 Test1)) in
                  (exist_3 [x2: Z][y2: Z][result3: unit](`0 < x2` /\
                  `0 < y2` /\ `(gcd x2 y2) = (gcd a b)`) /\ `x2 = y2` 
                  x1 y1 result2 Post5) end) (max result result0) result
            result0 (refl_equal ? (max result result0))
            (gcd1_po_5 a b Pre4 result Post1 result0 Post2)) in
        let (result2, Post12) = (exist_1 [result2: Z]`result2 = (gcd a b)` 
          x0 (gcd1_po_6 a b Pre4 result Post1 result0 Post2 x0 y0 Post5)) in
        (exist_3 [x1: Z][y1: Z][result3: Z]`result3 = (gcd a b)` x0 y0
        result2 Post12) in
      (exist_2 [x1: Z][result2: Z]`result2 = (gcd a b)` x0 result1 Post9) in
    (exist_1 [result1: Z]`result1 = (gcd a b)` result0 Post8).

Lemma gcd2_po_1 : 
  (a: Z)
  (b: Z)
  (Pre5: `a >= 0` /\ `b >= 0`)
  (result: Z)
  (Post1: result = a)
  (result0: Z)
  (Post2: result0 = b)
  (well_founded (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma gcd2_po_2 : 
  (a: Z)
  (b: Z)
  (Pre5: `a >= 0` /\ `b >= 0`)
  (result: Z)
  (Post1: result = a)
  (result0: Z)
  (Post2: result0 = b)
  (Variant1: Z)
  (x0: Z)
  (y0: Z)
  (Pre4: Variant1 = y0)
  (Pre3: `0 <= x0` /\ `0 <= y0` /\ `(gcd x0 y0) = (gcd a b)`)
  (Test2: `y0 <> 0`)
  ~(y0 = `0`).
Proof.
Intuition.
Save.

Lemma gcd2_po_3 : 
  (a: Z)
  (b: Z)
  (Pre5: `a >= 0` /\ `b >= 0`)
  (result: Z)
  (Post1: result = a)
  (result0: Z)
  (Post2: result0 = b)
  (Variant1: Z)
  (x0: Z)
  (y0: Z)
  (Pre4: Variant1 = y0)
  (Pre3: `0 <= x0` /\ `0 <= y0` /\ `(gcd x0 y0) = (gcd a b)`)
  (Test2: `y0 <> 0`)
  (Pre2: ~(y0 = `0`))
  (r: Z)
  (Post3: r = (Zmod x0 y0))
  (x1: Z)
  (Post4: x1 = y0)
  (y1: Z)
  (Post5: y1 = r)
  (`0 <= x1` /\ `0 <= y1` /\ `(gcd x1 y1) = (gcd a b)`) /\ (Zwf `0` y1 y0).
Proof.
Intuition.
Assert h_y0 : ~ `y0 = 0`. Assumption.
Assert h1_y0 : `y0 > 0`. Omega.
Generalize (Z_mod_lt x0 y0 h1_y0); Intro.
Rewrite Post5; Rewrite Post3; Tauto.
Rewrite Post4; Rewrite Post5; Rewrite Post3.
Rewrite <- H4; Auto.
Unfold Zwf.
Assert h_y0 : ~ `y0 = 0`. Assumption.
Assert h1_y0 : `y0 > 0`. Omega.
Generalize (Z_mod_lt x0 y0 h1_y0); Omega.
Save.

Lemma gcd2_po_4 : 
  (a: Z)
  (b: Z)
  (Pre5: `a >= 0` /\ `b >= 0`)
  (result: Z)
  (Post1: result = a)
  (result0: Z)
  (Post2: result0 = b)
  (Variant1: Z)
  (x0: Z)
  (y0: Z)
  (Pre4: Variant1 = y0)
  (Pre3: `0 <= x0` /\ `0 <= y0` /\ `(gcd x0 y0) = (gcd a b)`)
  (Test2: `y0 <> 0`)
  (x1: Z)
  (y1: Z)
  (Post7: (`0 <= x1` /\ `0 <= y1` /\ `(gcd x1 y1) = (gcd a b)`) /\
          (Zwf `0` y1 y0))
  (Zwf `0` y1 Variant1).
Proof.
Intuition.
Rewrite Pre4; Assumption.
Save.

Lemma gcd2_po_5 : 
  (a: Z)
  (b: Z)
  (Pre5: `a >= 0` /\ `b >= 0`)
  (result: Z)
  (Post1: result = a)
  (result0: Z)
  (Post2: result0 = b)
  `0 <= result` /\ `0 <= result0` /\ `(gcd result result0) = (gcd a b)`.
Proof.
Intuition.
Rewrite Post1; Rewrite Post2; Reflexivity.
Save.

Lemma gcd2_po_6 : 
  (a: Z)
  (b: Z)
  (Pre5: `a >= 0` /\ `b >= 0`)
  (result: Z)
  (Post1: result = a)
  (result0: Z)
  (Post2: result0 = b)
  (x0: Z)
  (y0: Z)
  (Post6: (`0 <= x0` /\ `0 <= y0` /\ `(gcd x0 y0) = (gcd a b)`) /\ `y0 = 0`)
  `x0 = (gcd a b)`.
Proof.
Intuition.
Rewrite <- H5; Rewrite H2; Auto.
Save.

Definition gcd2 := (* validation *)
  [a: Z; b: Z; Pre5: `a >= 0` /\ `b >= 0`]
    let (result, Post1) = (exist_1 [result: Z]result = a a
      (refl_equal ? a)) in
    let (x0, result0, Post8) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = b b
        (refl_equal ? b)) in
      let (x0, y0, result1, Post9) =
        let (x0, y0, result1, Post6) =
          (well_founded_induction Z (Zwf ZERO)
            (gcd2_po_1 a b Pre5 result Post1 result0 Post2) [Variant1: Z]
            (x0: Z)(y0: Z)(_: Variant1 = y0)(_0: `0 <= x0` /\ `0 <= y0` /\
            `(gcd x0 y0) = (gcd a b)`)
            (sig_3 Z Z unit [x1: Z][y1: Z][result1: unit]((`0 <= x1` /\
             `0 <= y1` /\ `(gcd x1 y1) = (gcd a b)`) /\ `y1 = 0`))
            [Variant1: Z; wf1: (Variant2: Z)
             (Pre1: (Zwf `0` Variant2 Variant1))(x0: Z)(y0: Z)
             (_: Variant2 = y0)(_0: `0 <= x0` /\ `0 <= y0` /\
             `(gcd x0 y0) = (gcd a b)`)
             (sig_3 Z Z unit [x1: Z][y1: Z][result1: unit]((`0 <= x1` /\
              `0 <= y1` /\ `(gcd x1 y1) = (gcd a b)`) /\ `y1 = 0`));
             x0: Z; y0: Z; Pre4: Variant1 = y0; Pre3: `0 <= x0` /\
             `0 <= y0` /\ `(gcd x0 y0) = (gcd a b)`]
              let (result1, Bool1) =
                let (result3, Post10) = (Z_noteq_bool y0 `0`) in
                (exist_1 [result4: bool]
                (if result4 then `y0 <> 0` else `y0 = 0`) result3 Post10) in
              (Cases (btest
                      [result1:bool](if result1 then `y0 <> 0` else `y0 = 0`)
                      result1 Bool1) of
              | (left Test2) =>
                  let (x1, y1, result2, Post6) =
                    let (x1, y1, result2, Post7) =
                      let (x1, y1, result2, Post7) =
                        let Pre2 =
                          (gcd2_po_2 a b Pre5 result Post1 result0 Post2
                          Variant1 x0 y0 Pre4 Pre3 Test2) in
                        let (r, Post3) = (exist_1 [result2: Z]
                          result2 = (Zmod x0 y0) (Zmod x0 y0)
                          (refl_equal ? (Zmod x0 y0))) in
                        let (x1, y1, result2, Post7) =
                          let (x1, result2, Post4) =
                            let (result2, Post4) = (exist_1 [result2: Z]
                              result2 = y0 y0 (refl_equal ? y0)) in
                            (exist_2 [x2: Z][result3: unit]x2 = y0 result2 
                            tt Post4) in
                          let (y1, result3, Post5) =
                            let (result3, Post5) = (exist_1 [result3: Z]
                              result3 = r r (refl_equal ? r)) in
                            (exist_2 [y2: Z][result4: unit]y2 = r result3 
                            tt Post5) in
                          (exist_3 [x2: Z][y2: Z][result4: unit](`0 <= x2` /\
                          `0 <= y2` /\ `(gcd x2 y2) = (gcd a b)`) /\
                          (Zwf `0` y2 y0) x1 y1 result3
                          (gcd2_po_3 a b Pre5 result Post1 result0 Post2
                          Variant1 x0 y0 Pre4 Pre3 Test2 Pre2 r Post3 x1
                          Post4 y1 Post5)) in
                        (exist_3 [x2: Z][y2: Z][result3: unit](`0 <= x2` /\
                        `0 <= y2` /\ `(gcd x2 y2) = (gcd a b)`) /\
                        (Zwf `0` y2 y0) x1 y1 result2 Post7) in
                      (exist_3 [x2: Z][y2: Z][result3: unit](`0 <= x2` /\
                      `0 <= y2` /\ `(gcd x2 y2) = (gcd a b)`) /\
                      (Zwf `0` y2 y0) x1 y1 result2 Post7) in
                    ((wf1 y1)
                      (gcd2_po_4 a b Pre5 result Post1 result0 Post2 Variant1
                      x0 y0 Pre4 Pre3 Test2 x1 y1 Post7) x1 y1
                      (refl_equal ? y1) (proj1 ? ? Post7)) in
                  (exist_3 [x2: Z][y2: Z][result3: unit](`0 <= x2` /\
                  `0 <= y2` /\ `(gcd x2 y2) = (gcd a b)`) /\ `y2 = 0` 
                  x1 y1 result2 Post6)
              | (right Test1) =>
                  let (x1, y1, result2, Post6) = (exist_3 [x1: Z][y1: Z]
                    [result2: unit](`0 <= x1` /\ `0 <= y1` /\
                    `(gcd x1 y1) = (gcd a b)`) /\ `y1 = 0` x0 y0 tt
                    (conj ? ? Pre3 Test1)) in
                  (exist_3 [x2: Z][y2: Z][result3: unit](`0 <= x2` /\
                  `0 <= y2` /\ `(gcd x2 y2) = (gcd a b)`) /\ `y2 = 0` 
                  x1 y1 result2 Post6) end) result0 result result0
            (refl_equal ? result0)
            (gcd2_po_5 a b Pre5 result Post1 result0 Post2)) in
        let (result2, Post11) = (exist_1 [result2: Z]`result2 = (gcd a b)` 
          x0 (gcd2_po_6 a b Pre5 result Post1 result0 Post2 x0 y0 Post6)) in
        (exist_3 [x1: Z][y1: Z][result3: Z]`result3 = (gcd a b)` x0 y0
        result2 Post11) in
      (exist_2 [x1: Z][result2: Z]`result2 = (gcd a b)` x0 result1 Post9) in
    (exist_1 [result1: Z]`result1 = (gcd a b)` result0 Post8).

