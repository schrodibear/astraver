(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Omega.
Require Zdiv.
Require ZArithRing.

Lemma mult_po_1 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma mult_po_2 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
  (Test4: `a0 <> 0`)
  ~(`2` = `0`).
Proof.
Intros; Omega.
Save.

Lemma mult_po_3 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
  (Test4: `a0 <> 0`)
  (Test3: `(Zmod a0 2) = 1`)
  (p1: Z)
  (Post4: p1 = `p0 + b0`)
  ((a:Z)
   (a = (Zdiv a0 `2`) ->
    ((b:Z)
     (b = `2 * b0` -> `a >= 0` /\ `p1 + a * b = x * y` /\ (Zwf `0` a a0))))).
Proof.
Intuition.
Rewrite H3; Apply Z_div_ge0; Omega.
Rewrite (Z_div_mod_eq a0 `2`) in H2.
Rewrite <- H2.
Rewrite Post4.
Rewrite H3. Rewrite H4.
Rewrite Test3.
Ring.
Omega.
Unfold Zwf. 
Repeat Split; Try Omega.
Rewrite H3; Apply Zge_le; Apply Z_div_ge0; Omega.
Rewrite H3; Apply Z_div_lt; Try Omega.
Cut ~`a0 = 0`; [ Intro; Omega | Assumption ].
Save.

Lemma mult_po_4 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
  (Test4: `a0 <> 0`)
  (Test2: `(Zmod a0 2) <> 1`)
  ((a:Z)
   (a = (Zdiv a0 `2`) ->
    ((b:Z)
     (b = `2 * b0` -> `a >= 0` /\ `p0 + a * b = x * y` /\ (Zwf `0` a a0))))).
Proof.
Intuition.
Rewrite H3; Apply Z_div_ge0; Try Omega.
Rewrite (Z_div_mod_eq a0 `2`) in H2.
Rewrite <- H2.
Rewrite H3. Rewrite H4.
Replace `a0%2` with `0`.
Ring.
Cut `2 > 0`; [ Intro h | Omega ].
Generalize (Z_mod_lt a0 `2` h).
Cut ~`a0%2 = 1`; Intros; Try Omega.
Assumption.
Omega.
Unfold Zwf.
Repeat Split; Try Omega.
Rewrite H3; Apply Zge_le; Apply Z_div_ge0; Omega.
Rewrite H3; Apply Z_div_lt; Try Omega.
Cut ~`a0 = 0`; [ Intro; Omega | Assumption ].
Save.

Lemma mult_po_5 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
  (Test4: `a0 <> 0`)
  (p1: Z)
  (Post12: ((a:Z)
            (a = (Zdiv a0 `2`) ->
             ((b:Z)
              (b = `2 * b0` -> `a >= 0` /\ `p1 + a * b = x * y` /\
               (Zwf `0` a a0))))))
  ~(`2` = `0`).
Proof.
Intros; Omega.
Save.

Lemma mult_po_6 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
  (Test4: `a0 <> 0`)
  (p1: Z)
  (Post12: ((a:Z)
            (a = (Zdiv a0 `2`) ->
             ((b:Z)
              (b = `2 * b0` -> `a >= 0` /\ `p1 + a * b = x * y` /\
               (Zwf `0` a a0))))))
  (Pre3: ~(`2` = `0`))
  (a1: Z)
  (Post5: a1 = (Zdiv a0 `2`))
  (b1: Z)
  (Post6: b1 = `2 * b0`)
  `a1 >= 0` /\ `p1 + a1 * b1 = x * y` /\ (Zwf `0` a1 a0).
Proof.
Intuition.
Save.

Lemma mult_po_7 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
  (Test4: `a0 <> 0`)
  (a1: Z)
  (b1: Z)
  (p1: Z)
  (Inv0: `a1 >= 0` /\ `p1 + a1 * b1 = x * y` /\ (Zwf `0` a1 a0))
  (Zwf `0` a1 Variant1).
Proof.
Intros; Rewrite Pre4; Tauto.
Save.

Lemma mult_po_8 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
  (Test4: `a0 <> 0`)
  (a1: Z)
  (b1: Z)
  (p1: Z)
  (Inv0: `a1 >= 0` /\ `p1 + a1 * b1 = x * y` /\ (Zwf `0` a1 a0))
  `a1 >= 0` /\ `p1 + a1 * b1 = x * y`.
Proof.
Intuition.
Save.

Lemma mult_po_9 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
  (Test1: `a0 = 0`)
  `a0 >= 0` /\ `p0 + a0 * b0 = x * y` /\ `a0 = 0`.
Proof.
Intuition.
Save.

Lemma mult_po_10 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  `result >= 0` /\ `result1 + result * result0 = x * y`.
Proof.
Intuition.
Rewrite Post1; Rewrite Post2; Rewrite Post3; Ring.
Save.

Lemma mult_po_11 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y` /\ `a0 = 0`)
  `p0 = x * y`.
Proof.
Intuition.
Rewrite H4 in H3.
Rewrite <- H3.
Ring.
Save.

Definition mult := (* validation *)
  [x: Z; y: Z; Pre5: `x >= 0` /\ `y >= 0`]
    let (result, Post1) = (exist_1 [result: Z]result = x x
      (refl_equal ? x)) in
    let (a0, result0, Post8) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = y y
        (refl_equal ? y)) in
      let (a0, b0, result1, Post9) =
        let (result1, Post3) = (exist_1 [result1: Z]result1 = `0` `0`
          (refl_equal ? `0`)) in
        let (a0, b0, p0, result2, Post10) =
          let (a0, b0, p0, result2, Inv) =
            (well_founded_induction Z (Zwf ZERO)
              (mult_po_1 x y Pre5 result Post1 result0 Post2 result1 Post3)
              [Variant1: Z](a0: Z)(b0: Z)(p0: Z)(_: Variant1 = a0)
              (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
              (sig_4 Z Z Z unit [a1: Z][b1: Z][p1: Z][result2: unit]
               (`a1 >= 0` /\ `p1 + a1 * b1 = x * y` /\ `a1 = 0`))
              [Variant1: Z; wf1: (Variant2: Z)
               (Pre1: (Zwf `0` Variant2 Variant1))(a0: Z)(b0: Z)(p0: Z)
               (_: Variant2 = a0)(Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
               (sig_4 Z Z Z unit [a1: Z][b1: Z][p1: Z][result2: unit]
                (`a1 >= 0` /\ `p1 + a1 * b1 = x * y` /\ `a1 = 0`));
               a0: Z; b0: Z; p0: Z; Pre4: Variant1 = a0; Inv: `a0 >= 0` /\
               `p0 + a0 * b0 = x * y`]
                let (result2, Bool1) =
                  let (result4, Post11) = (Z_noteq_bool a0 `0`) in
                  (exist_1 [result5: bool]
                  (if result5 then `a0 <> 0` else `a0 = 0`) result4 Post11) in
                (Cases (btest
                        [result2:bool](if result2 then `a0 <> 0`
                                       else `a0 = 0`)
                        result2 Bool1) of
                | (left Test4) =>
                    let (a1, b1, p1, result3, Inv0) =
                      let (a1, b1, p1, result3, Inv0) =
                        let (p1, result3, Post12) =
                          let (result3, Bool2) =
                            let result4 =
                              let Pre2 =
                                (mult_po_2 x y Pre5 result Post1 result0
                                Post2 result1 Post3 Variant1 a0 b0 p0 Pre4
                                Inv Test4) in
                              (Z_eq_bool (Zmod a0 `2`)) in
                            let (result5, Post13) = (result4 `1`) in
                            (exist_1 [result6: bool]
                            (if result6 then `(Zmod a0 2) = 1`
                             else `(Zmod a0 2) <> 1`) result5
                            Post13) in
                          (Cases (btest
                                  [result3:bool](if result3
                                                 then `(Zmod a0 2) = 1`
                                                 else `(Zmod a0 2) <> 1`)
                                  result3 Bool2) of
                          | (left Test3) =>
                              let (p1, result4, Post4) =
                                let (result4, Post4) = (exist_1 [result4: Z]
                                  result4 = `p0 + b0` `p0 + b0`
                                  (refl_equal ? `p0 + b0`)) in
                                (exist_2 [p2: Z][result5: unit]
                                p2 = `p0 + b0` result4 tt Post4) in
                              (exist_2 [p2: Z][result5: unit]
                              ((a:Z)
                               (a = (Zdiv a0 `2`) ->
                                ((b:Z)
                                 (b = `2 * b0` -> `a >= 0` /\
                                  `p2 + a * b = x * y` /\ (Zwf `0` a a0))))) 
                              p1 result4
                              (mult_po_3 x y Pre5 result Post1 result0 Post2
                              result1 Post3 Variant1 a0 b0 p0 Pre4 Inv Test4
                              Test3 p1 Post4))
                          | (right Test2) =>
                              let (result4, Post14) =
                                (exist_1 [result4: unit]
                                ((a:Z)
                                 (a = (Zdiv a0 `2`) ->
                                  ((b:Z)
                                   (b = `2 * b0` -> `a >= 0` /\
                                    `p0 + a * b = x * y` /\ (Zwf `0` a a0))))) 
                                tt
                                (mult_po_4 x y Pre5 result Post1 result0
                                Post2 result1 Post3 Variant1 a0 b0 p0 Pre4
                                Inv Test4 Test2)) in
                              (exist_2 [p1: Z][result5: unit]
                              ((a:Z)
                               (a = (Zdiv a0 `2`) ->
                                ((b:Z)
                                 (b = `2 * b0` -> `a >= 0` /\
                                  `p1 + a * b = x * y` /\ (Zwf `0` a a0))))) 
                              p0 result4 Post14) end) in
                        let Pre3 =
                          (mult_po_5 x y Pre5 result Post1 result0 Post2
                          result1 Post3 Variant1 a0 b0 p0 Pre4 Inv Test4 p1
                          Post12) in
                        let (a1, result4, Post5) =
                          let (result4, Post5) = (exist_1 [result4: Z]
                            result4 = (Zdiv a0 `2`) (Zdiv a0 `2`)
                            (refl_equal ? (Zdiv a0 `2`))) in
                          (exist_2 [a2: Z][result5: unit]
                          a2 = (Zdiv a0 `2`) result4 tt Post5) in
                        let (b1, result5, Post6) =
                          let (result5, Post6) = (exist_1 [result5: Z]
                            result5 = `2 * b0` `2 * b0`
                            (refl_equal ? `2 * b0`)) in
                          (exist_2 [b2: Z][result6: unit]
                          b2 = `2 * b0` result5 tt Post6) in
                        (exist_4 [a2: Z][b2: Z][p2: Z][result6: unit]
                        `a2 >= 0` /\ `p2 + a2 * b2 = x * y` /\
                        (Zwf `0` a2 a0) a1 b1 p1 result5
                        (mult_po_6 x y Pre5 result Post1 result0 Post2
                        result1 Post3 Variant1 a0 b0 p0 Pre4 Inv Test4 p1
                        Post12 Pre3 a1 Post5 b1 Post6)) in
                      ((wf1 a1)
                        (mult_po_7 x y Pre5 result Post1 result0 Post2
                        result1 Post3 Variant1 a0 b0 p0 Pre4 Inv Test4 a1 b1
                        p1 Inv0) a1 b1 p1 (refl_equal ? a1)
                        (mult_po_8 x y Pre5 result Post1 result0 Post2
                        result1 Post3 Variant1 a0 b0 p0 Pre4 Inv Test4 a1 b1
                        p1 Inv0)) in
                    (exist_4 [a2: Z][b2: Z][p2: Z][result4: unit]`a2 >= 0` /\
                    `p2 + a2 * b2 = x * y` /\ `a2 = 0` a1 b1 p1 result3 Inv0)
                | (right Test1) =>
                    let (a1, b1, p1, result3, Inv0) = (exist_4 [a1: Z][b1: Z]
                      [p1: Z][result3: unit]`a1 >= 0` /\
                      `p1 + a1 * b1 = x * y` /\ `a1 = 0` a0 b0 p0 tt
                      (mult_po_9 x y Pre5 result Post1 result0 Post2 result1
                      Post3 Variant1 a0 b0 p0 Pre4 Inv Test1)) in
                    (exist_4 [a2: Z][b2: Z][p2: Z][result4: unit]`a2 >= 0` /\
                    `p2 + a2 * b2 = x * y` /\ `a2 = 0` a1 b1 p1 result3 Inv0) end)
              result result result0 result1 (refl_equal ? result)
              (mult_po_10 x y Pre5 result Post1 result0 Post2 result1 Post3)) in
          let (result3, Post15) = (exist_1 [result3: Z]`result3 = x * y` 
            p0
            (mult_po_11 x y Pre5 result Post1 result0 Post2 result1 Post3 a0
            b0 p0 Inv)) in
          (exist_4 [a1: Z][b1: Z][p1: Z][result4: Z]`result4 = x * y` 
          a0 b0 p0 result3 Post15) in
        (exist_3 [a1: Z][b1: Z][result3: Z]`result3 = x * y` a0 b0 result2
        Post10) in
      (exist_2 [a1: Z][result2: Z]`result2 = x * y` a0 result1 Post9) in
    (exist_1 [result1: Z]`result1 = x * y` result0 Post8).

