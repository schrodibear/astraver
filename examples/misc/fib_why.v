(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

Parameter F : Z -> Z.
Axiom F_0 : (F `0`) = `1`.
Axiom F_1 : (F `1`) = `1`.
Axiom F_n : (n:Z) `n >= 2` -> `(F n) = (F (n-1)) + (F (n-2))`.
Hints Resolve F_0 F_1 F_n.

Lemma fib1_po_1 : 
  (n: Z)
  (Pre8: `n >= 0`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma fib1_po_2 : 
  (Variant1: Z)
  (n: Z)
  (Pre7: Variant1 = n)
  (Pre6: `n >= 0`)
  (Test2: `n <= 1`)
  `1 = (F n)`.
Proof.
Intros.
Assert `n = 0` \/ `n = 1`; 
Intuition Try (Rewrite H0; Auto with *).
Omega.
Save.

Lemma fib1_po_3 : 
  (Variant1: Z)
  (n: Z)
  (Pre7: Variant1 = n)
  (Pre6: `n >= 0`)
  (Test1: `n > 1`)
  `n - 2 >= 0`.
Proof.
Intros; Omega.
Save.

Lemma fib1_po_4 : 
  (Variant1: Z)
  (n: Z)
  (Pre7: Variant1 = n)
  (Pre6: `n >= 0`)
  (Test1: `n > 1`)
  (Pre3: `n - 2 >= 0`)
  (Zwf `0` `n - 2` Variant1).
Proof.
Intros; Unfold Zwf; Omega.
Save.

Lemma fib1_po_5 : 
  (Variant1: Z)
  (n: Z)
  (Pre7: Variant1 = n)
  (Pre6: `n >= 0`)
  (Test1: `n > 1`)
  (aux_4: Z)
  (Post4: `aux_4 = (F n - 2)`)
  `n - 1 >= 0`.
Proof.
Intros; Omega.
Save.

Lemma fib1_po_6 : 
  (Variant1: Z)
  (n: Z)
  (Pre7: Variant1 = n)
  (Pre6: `n >= 0`)
  (Test1: `n > 1`)
  (aux_4: Z)
  (Post4: `aux_4 = (F n - 2)`)
  (Pre5: `n - 1 >= 0`)
  (Zwf `0` `n - 1` Variant1).
Proof.
Intros; Unfold Zwf; Omega.
Save.

Lemma fib1_po_7 : 
  (Variant1: Z)
  (n: Z)
  (Pre7: Variant1 = n)
  (Pre6: `n >= 0`)
  (Test1: `n > 1`)
  (aux_4: Z)
  (Post4: `aux_4 = (F n - 2)`)
  (aux_3: Z)
  (Post7: `aux_3 = (F n - 1)`)
  `aux_3 + aux_4 = (F n)`.
Proof.
Intros.
Rewrite Post4; Rewrite Post7.
Symmetry; Auto with *.
Save.

Definition fib1 := (* validation *)
  [n: Z; Pre8: `n >= 0`]
    (well_founded_induction Z (Zwf ZERO) (fib1_po_1 n Pre8) [Variant1: Z]
      (n: Z)(_: Variant1 = n)(_: `n >= 0`)
      (sig_1 Z [result:Z](`result = (F n)`))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (n: Z)(_: Variant2 = n)(_: `n >= 0`)
       (sig_1 Z [result:Z](`result = (F n)`)); n: Z; Pre7: Variant1 = n;
       Pre6: `n >= 0`]
        let (result, Bool1) =
          let (result1, Post2) = (Z_le_gt_bool n `1`) in
          (exist_1 [result2: bool]
          (if result2 then `n <= 1` else `n > 1`) result1 Post2) in
        (Cases (btest [result:bool](if result then `n <= 1` else `n > 1`)
                result Bool1) of
        | (left Test2) =>
            let (result0, Post10) = (exist_1 [result0: Z]
              `result0 = (F n)` `1`
              (fib1_po_2 Variant1 n Pre7 Pre6 Test2)) in
            (exist_1 [result1: Z]`result1 = (F n)` result0 Post10)
        | (right Test1) =>
            let (result0, Post3) =
              let (aux_4, Post4) =
                let Pre3 = (fib1_po_3 Variant1 n Pre7 Pre6 Test1) in
                let (result2, Post5) =
                  ((wf1 `n - 2`) (fib1_po_4 Variant1 n Pre7 Pre6 Test1 Pre3)
                    `n - 2` (refl_equal ? `n - 2`) Pre3) in
                (exist_1 [result3: Z]`result3 = (F n - 2)` result2 Post5) in
              let (result0, Post6) =
                let (aux_3, Post7) =
                  let Pre5 =
                    (fib1_po_5 Variant1 n Pre7 Pre6 Test1 aux_4 Post4) in
                  let (result2, Post8) =
                    ((wf1 `n - 1`)
                      (fib1_po_6 Variant1 n Pre7 Pre6 Test1 aux_4 Post4 Pre5)
                      `n - 1` (refl_equal ? `n - 1`) Pre5) in
                  (exist_1 [result3: Z]`result3 = (F n - 1)` result2 Post8) in
                let (result0, Post9) = (exist_1 [result0: Z]
                  `result0 = (F n)` `aux_3 + aux_4`
                  (fib1_po_7 Variant1 n Pre7 Pre6 Test1 aux_4 Post4 aux_3
                  Post7)) in
                (exist_1 [result1: Z]`result1 = (F n)` result0 Post9) in
              (exist_1 [result1: Z]`result1 = (F n)` result0 Post6) in
            (exist_1 [result1: Z]`result1 = (F n)` result0 Post3) end) 
      n n (refl_equal ? n) Pre8).

Lemma fib2_aux_po_1 : 
  (n: Z)
  (x: Z)
  (fx: Z)
  (fx_1: Z)
  (Pre6: `1 <= x` /\ `x <= n` /\ `fx = (F x)` /\ `fx_1 = (F x - 1)`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma fib2_aux_po_2 : 
  (Variant1: Z)
  (n: Z)
  (x: Z)
  (fx: Z)
  (fx_1: Z)
  (Pre5: Variant1 = `n - x`)
  (Pre4: `1 <= x` /\ `x <= n` /\ `fx = (F x)` /\ `fx_1 = (F x - 1)`)
  (Test2: `x = n`)
  `fx = (F n)`.
Proof.
Intuition.
Rewrite <- Test2; Assumption.
Save.

Lemma fib2_aux_po_3 : 
  (Variant1: Z)
  (n: Z)
  (x: Z)
  (fx: Z)
  (fx_1: Z)
  (Pre5: Variant1 = `n - x`)
  (Pre4: `1 <= x` /\ `x <= n` /\ `fx = (F x)` /\ `fx_1 = (F x - 1)`)
  (Test1: `x <> n`)
  `1 <= x + 1` /\ `x + 1 <= n` /\ `fx + fx_1 = (F x + 1)` /\
  `fx = (F x + 1 - 1)`.
Proof.
Intuition.
Assert ~`x=n`; [ Assumption | Omega ].
Rewrite H0; Rewrite H3; Symmetry.
Generalize H. Replace x with `(x+1)-1`. Generalize `x+1`.
Intros; Ring `z-1+1`; Replace `z-1-1` with `z-2`. 
Auto with *.
Omega.
Omega.
Ring `x+1-1`; Trivial.
Save.

Lemma fib2_aux_po_4 : 
  (Variant1: Z)
  (n: Z)
  (x: Z)
  (fx: Z)
  (fx_1: Z)
  (Pre5: Variant1 = `n - x`)
  (Pre4: `1 <= x` /\ `x <= n` /\ `fx = (F x)` /\ `fx_1 = (F x - 1)`)
  (Test1: `x <> n`)
  (Pre3: `1 <= x + 1` /\ `x + 1 <= n` /\ `fx + fx_1 = (F x + 1)` /\
         `fx = (F x + 1 - 1)`)
  (Zwf `0` `n - (x + 1)` Variant1).
Proof.
Intuition.
Unfold Zwf; Omega.
Save.

Definition fib2_aux := (* validation *)
  [n: Z; x: Z; fx: Z; fx_1: Z; Pre6: `1 <= x` /\ `x <= n` /\ `fx = (F x)` /\
   `fx_1 = (F x - 1)`]
    (well_founded_induction Z (Zwf ZERO) (fib2_aux_po_1 n x fx fx_1 Pre6)
      [Variant1: Z](n: Z)(x: Z)(fx: Z)(fx_1: Z)(_: Variant1 = `n - x`)
      (_: `1 <= x` /\ `x <= n` /\ `fx = (F x)` /\ `fx_1 = (F x - 1)`)
      (sig_1 Z [result:Z](`result = (F n)`))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (n: Z)(x: Z)(fx: Z)(fx_1: Z)(_: Variant2 = `n - x`)(_: `1 <= x` /\
       `x <= n` /\ `fx = (F x)` /\ `fx_1 = (F x - 1)`)
       (sig_1 Z [result:Z](`result = (F n)`)); n: Z; x: Z; fx: Z; fx_1: Z;
       Pre5: Variant1 = `n - x`; Pre4: `1 <= x` /\ `x <= n` /\
       `fx = (F x)` /\ `fx_1 = (F x - 1)`]
        let (result, Bool1) =
          let (result1, Post2) = (Z_eq_bool x n) in
          (exist_1 [result2: bool]
          (if result2 then `x = n` else `x <> n`) result1 Post2) in
        (Cases (btest [result:bool](if result then `x = n` else `x <> n`)
                result Bool1) of
        | (left Test2) =>
            let (result0, Post5) = (exist_1 [result0: Z]`result0 = (F n)` 
              fx (fib2_aux_po_2 Variant1 n x fx fx_1 Pre5 Pre4 Test2)) in
            (exist_1 [result1: Z]`result1 = (F n)` result0 Post5)
        | (right Test1) =>
            let (result0, Post3) =
              let Pre3 =
                (fib2_aux_po_3 Variant1 n x fx fx_1 Pre5 Pre4 Test1) in
              let (result2, Post4) =
                ((wf1 `n - (x + 1)`)
                  (fib2_aux_po_4 Variant1 n x fx fx_1 Pre5 Pre4 Test1 Pre3) 
                  n `x + 1` `fx + fx_1` fx (refl_equal ? `n - (x + 1)`) Pre3) in
              (exist_1 [result3: Z]`result3 = (F n)` result2 Post4) in
            (exist_1 [result1: Z]`result1 = (F n)` result0 Post3) end)
      `n - x` n x fx fx_1 (refl_equal ? `n - x`) Pre6).

Lemma fib2_po_1 : 
  (n: Z)
  (Pre2: `n >= 0`)
  (Test2: `n <= 1`)
  `1 = (F n)`.
Proof.
Intuition.
Assert h: `n=0` \/ `n=1`. Omega.
Intuition; Rewrite H; Auto with *.
Save.

Lemma fib2_po_2 : 
  (n: Z)
  (Pre2: `n >= 0`)
  (Test1: `n > 1`)
  `1 <= 1` /\ `1 <= n` /\ `1 = (F 1)` /\ `1 = (F 1 - 1)`.
Proof.
Intuition.
Save.

Definition fib2 := (* validation *)
  [n: Z; Pre2: `n >= 0`]
    let (result, Bool1) =
      let (result1, Post2) = (Z_le_gt_bool n `1`) in
      (exist_1 [result2: bool](if result2 then `n <= 1` else `n > 1`) 
      result1 Post2) in
    (Cases (btest [result:bool](if result then `n <= 1` else `n > 1`) result
            Bool1) of
    | (left Test2) =>
        let (result0, Post5) = (exist_1 [result0: Z]`result0 = (F n)` 
          `1` (fib2_po_1 n Pre2 Test2)) in
        (exist_1 [result1: Z]`result1 = (F n)` result0 Post5)
    | (right Test1) =>
        let (result0, Post3) =
          let Pre1 = (fib2_po_2 n Pre2 Test1) in
          let (result2, Post4) = (fib2_aux n `1` `1` `1` Pre1) in
          (exist_1 [result3: Z]`result3 = (F n)` result2 Post4) in
        (exist_1 [result1: Z]`result1 = (F n)` result0 Post3) end).

Lemma fib3_po_1 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (result: Z)
  (Post1: result = `1`)
  (result0: Z)
  (Post2: result0 = `1`)
  (result1: Z)
  (Post3: result1 = `1`)
  (Test4: `n > 0`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma fib3_po_2 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (result: Z)
  (Post1: result = `1`)
  (result0: Z)
  (Post2: result0 = `1`)
  (result1: Z)
  (Post3: result1 = `1`)
  (Test4: `n > 0`)
  (Variant1: Z)
  (k0: Z)
  (x0: Z)
  (y0: Z)
  (Pre3: Variant1 = `n - k0`)
  (Pre2: `1 <= k0` /\ `k0 <= n` /\ `x0 = (F k0)` /\ `y0 = (F k0 - 1)`)
  (Test3: `k0 < n`)
  (t: Z)
  (Post4: t = y0)
  (y1: Z)
  (Post5: y1 = x0)
  (x1: Z)
  (Post6: x1 = `x0 + t`)
  (k1: Z)
  (Post7: k1 = `k0 + 1`)
  `1 <= k1` /\ `k1 <= n` /\ `x1 = (F k1)` /\ `y1 = (F k1 - 1)` /\
  (Zwf `0` `n - k1` `n - k0`).
Proof.
Intuition.
Rewrite Post7; Rewrite Post6; Rewrite Post4; Rewrite H0; Rewrite H3.
Symmetry.
Generalize H. Replace k0 with `(k0+1)-1`. Generalize `k0+1`.
Intros; Ring `z-1+1`; Replace `z-1-1` with `z-2`. 
Auto with *.
Omega.
Omega.
Rewrite Post7; Ring `k0+1-1`; Trivial.
Rewrite Post5; Assumption.
Unfold Zwf; Omega.
Save.

Lemma fib3_po_3 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (result: Z)
  (Post1: result = `1`)
  (result0: Z)
  (Post2: result0 = `1`)
  (result1: Z)
  (Post3: result1 = `1`)
  (Test4: `n > 0`)
  (Variant1: Z)
  (k0: Z)
  (x0: Z)
  (y0: Z)
  (Pre3: Variant1 = `n - k0`)
  (Pre2: `1 <= k0` /\ `k0 <= n` /\ `x0 = (F k0)` /\ `y0 = (F k0 - 1)`)
  (Test3: `k0 < n`)
  (k1: Z)
  (x1: Z)
  (y1: Z)
  (Post9: `1 <= k1` /\ `k1 <= n` /\ `x1 = (F k1)` /\ `y1 = (F k1 - 1)` /\
          (Zwf `0` `n - k1` `n - k0`))
  (Zwf `0` `n - k1` Variant1).
Proof.
Intuition.
Rewrite Pre3; Assumption.
Save.

Lemma fib3_po_4 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (result: Z)
  (Post1: result = `1`)
  (result0: Z)
  (Post2: result0 = `1`)
  (result1: Z)
  (Post3: result1 = `1`)
  (Test4: `n > 0`)
  (Variant1: Z)
  (k0: Z)
  (x0: Z)
  (y0: Z)
  (Pre3: Variant1 = `n - k0`)
  (Pre2: `1 <= k0` /\ `k0 <= n` /\ `x0 = (F k0)` /\ `y0 = (F k0 - 1)`)
  (Test3: `k0 < n`)
  (k1: Z)
  (x1: Z)
  (y1: Z)
  (Post9: `1 <= k1` /\ `k1 <= n` /\ `x1 = (F k1)` /\ `y1 = (F k1 - 1)` /\
          (Zwf `0` `n - k1` `n - k0`))
  `1 <= k1` /\ `k1 <= n` /\ `x1 = (F k1)` /\ `y1 = (F k1 - 1)`.
Proof.
Intuition.
Save.

Lemma fib3_po_5 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (result: Z)
  (Post1: result = `1`)
  (result0: Z)
  (Post2: result0 = `1`)
  (result1: Z)
  (Post3: result1 = `1`)
  (Test4: `n > 0`)
  (Variant1: Z)
  (k0: Z)
  (x0: Z)
  (y0: Z)
  (Pre3: Variant1 = `n - k0`)
  (Pre2: `1 <= k0` /\ `k0 <= n` /\ `x0 = (F k0)` /\ `y0 = (F k0 - 1)`)
  (Test2: `k0 >= n`)
  `1 <= k0` /\ `k0 <= n` /\ `x0 = (F k0)` /\ `y0 = (F k0 - 1)` /\ `k0 >= n`.
Proof.
Intuition.
Save.

Lemma fib3_po_6 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (result: Z)
  (Post1: result = `1`)
  (result0: Z)
  (Post2: result0 = `1`)
  (result1: Z)
  (Post3: result1 = `1`)
  (Test4: `n > 0`)
  `1 <= result` /\ `result <= n` /\ `result0 = (F result)` /\
  `result1 = (F result - 1)`.
Proof.
Intuition.
Rewrite Post1; Rewrite Post2.
Auto with *.
Rewrite Post1; Rewrite Post3.
Auto with *.
Save.

Lemma fib3_po_7 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (result: Z)
  (Post1: result = `1`)
  (result0: Z)
  (Post2: result0 = `1`)
  (result1: Z)
  (Post3: result1 = `1`)
  (Test4: `n > 0`)
  (k0: Z)
  (x0: Z)
  (y0: Z)
  (Post8: `1 <= k0` /\ `k0 <= n` /\ `x0 = (F k0)` /\ `y0 = (F k0 - 1)` /\
          `k0 >= n`)
  `x0 = (F n)`.
Proof.
Intuition.
Replace n with k0. Auto. Omega.
Save.

Lemma fib3_po_8 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (result: Z)
  (Post1: result = `1`)
  (result0: Z)
  (Post2: result0 = `1`)
  (result1: Z)
  (Post3: result1 = `1`)
  (Test1: `n <= 0`)
  `result0 = (F n)`.
Proof.
Intuition.
Rewrite Post2. Replace n  with `0`. Auto.
Omega.
Save.

Definition fib3 := (* validation *)
  [n: Z; Pre4: `n >= 0`]
    let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
      (refl_equal ? `1`)) in
    let (k0, result0, Post11) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = `1` `1`
        (refl_equal ? `1`)) in
      let (k0, x0, result1, Post12) =
        let (result1, Post3) = (exist_1 [result1: Z]result1 = `1` `1`
          (refl_equal ? `1`)) in
        let (k0, x0, y0, result2, Post13) =
          let (k0, x0, y0, result2, Post14) =
            let (result2, Bool2) =
              let (result4, Post15) = (Z_gt_le_bool n `0`) in
              (exist_1 [result5: bool]
              (if result5 then `n > 0` else `n <= 0`) result4 Post15) in
            (Cases (btest
                    [result2:bool](if result2 then `n > 0` else `n <= 0`)
                    result2 Bool2) of
            | (left Test4) =>
                let (k0, x0, y0, result3, Post8) =
                  (well_founded_induction Z (Zwf ZERO)
                    (fib3_po_1 n Pre4 result Post1 result0 Post2 result1
                    Post3 Test4) [Variant1: Z](k0: Z)(x0: Z)(y0: Z)
                    (_: Variant1 = `n - k0`)(_: `1 <= k0` /\ `k0 <= n` /\
                    `x0 = (F k0)` /\ `y0 = (F k0 - 1)`)
                    (sig_4 Z Z Z unit [k1:Z][x1:Z][y1:Z][result:unit]
                     (`1 <= k1` /\ `k1 <= n` /\ `x1 = (F k1)` /\
                     `y1 = (F k1 - 1)` /\ `k1 >= n`))
                    [Variant1: Z; wf1: (Variant2: Z)
                     (Pre1: (Zwf `0` Variant2 Variant1))(k0: Z)(x0: Z)(y0: Z)
                     (_: Variant2 = `n - k0`)(_: `1 <= k0` /\ `k0 <= n` /\
                     `x0 = (F k0)` /\ `y0 = (F k0 - 1)`)
                     (sig_4 Z Z Z unit [k1:Z][x1:Z][y1:Z][result:unit]
                      (`1 <= k1` /\ `k1 <= n` /\ `x1 = (F k1)` /\
                      `y1 = (F k1 - 1)` /\ `k1 >= n`));
                     k0: Z; x0: Z; y0: Z; Pre3: Variant1 = `n - k0`;
                     Pre2: `1 <= k0` /\ `k0 <= n` /\ `x0 = (F k0)` /\
                     `y0 = (F k0 - 1)`]
                      let (result3, Bool1) =
                        let (result5, Post17) = (Z_lt_ge_bool k0 n) in
                        (exist_1 [result6: bool]
                        (if result6 then `k0 < n` else `k0 >= n`) result5
                        Post17) in
                      (Cases (btest
                              [result3:bool](if result3 then `k0 < n`
                                             else `k0 >= n`)
                              result3 Bool1) of
                      | (left Test3) =>
                          let (k1, x1, y1, result4, Post8) =
                            let (k1, x1, y1, result4, Post9) =
                              let (k1, x1, y1, result4, Post9) =
                                let (t, Post4) = (exist_1 [result4: Z]
                                  result4 = y0 y0 (refl_equal ? y0)) in
                                let (k1, x1, y1, result4, Post9) =
                                  let (y1, result4, Post5) =
                                    let (result4, Post5) =
                                      (exist_1 [result4: Z]result4 = x0 
                                      x0 (refl_equal ? x0)) in
                                    (exist_2 [y2: Z][result5: unit]
                                    y2 = x0 result4 tt Post5) in
                                  let (x1, result5, Post6) =
                                    let (result5, Post6) =
                                      (exist_1 [result5: Z]
                                      result5 = `x0 + t` `x0 + t`
                                      (refl_equal ? `x0 + t`)) in
                                    (exist_2 [x2: Z][result6: unit]
                                    x2 = `x0 + t` result5 tt Post6) in
                                  let (k1, result6, Post7) =
                                    let (result6, Post7) =
                                      (exist_1 [result6: Z]
                                      result6 = `k0 + 1` `k0 + 1`
                                      (refl_equal ? `k0 + 1`)) in
                                    (exist_2 [k2: Z][result7: unit]
                                    k2 = `k0 + 1` result6 tt Post7) in
                                  (exist_4 [k2: Z][x2: Z][y2: Z]
                                  [result7: unit]`1 <= k2` /\ `k2 <= n` /\
                                  `x2 = (F k2)` /\ `y2 = (F k2 - 1)` /\
                                  (Zwf `0` `n - k2` `n - k0`) k1 x1 y1
                                  result6
                                  (fib3_po_2 n Pre4 result Post1 result0
                                  Post2 result1 Post3 Test4 Variant1 k0 x0 y0
                                  Pre3 Pre2 Test3 t Post4 y1 Post5 x1 Post6
                                  k1 Post7)) in
                                (exist_4 [k2: Z][x2: Z][y2: Z][result5: unit]
                                `1 <= k2` /\ `k2 <= n` /\ `x2 = (F k2)` /\
                                `y2 = (F k2 - 1)` /\
                                (Zwf `0` `n - k2` `n - k0`) k1 x1 y1 
                                result4 Post9) in
                              (exist_4 [k2: Z][x2: Z][y2: Z][result5: unit]
                              `1 <= k2` /\ `k2 <= n` /\ `x2 = (F k2)` /\
                              `y2 = (F k2 - 1)` /\
                              (Zwf `0` `n - k2` `n - k0`) k1 x1 y1 result4
                              Post9) in
                            ((wf1 `n - k1`)
                              (fib3_po_3 n Pre4 result Post1 result0 Post2
                              result1 Post3 Test4 Variant1 k0 x0 y0 Pre3 Pre2
                              Test3 k1 x1 y1 Post9) k1 x1 y1
                              (refl_equal ? `n - k1`)
                              (fib3_po_4 n Pre4 result Post1 result0 Post2
                              result1 Post3 Test4 Variant1 k0 x0 y0 Pre3 Pre2
                              Test3 k1 x1 y1 Post9)) in
                          (exist_4 [k2: Z][x2: Z][y2: Z][result5: unit]
                          `1 <= k2` /\ `k2 <= n` /\ `x2 = (F k2)` /\
                          `y2 = (F k2 - 1)` /\ `k2 >= n` k1 x1 y1 result4
                          Post8)
                      | (right Test2) =>
                          let (k1, x1, y1, result4, Post8) = (exist_4 [k1: Z]
                            [x1: Z][y1: Z][result4: unit]`1 <= k1` /\
                            `k1 <= n` /\ `x1 = (F k1)` /\
                            `y1 = (F k1 - 1)` /\ `k1 >= n` k0 x0 y0 tt
                            (fib3_po_5 n Pre4 result Post1 result0 Post2
                            result1 Post3 Test4 Variant1 k0 x0 y0 Pre3 Pre2
                            Test2)) in
                          (exist_4 [k2: Z][x2: Z][y2: Z][result5: unit]
                          `1 <= k2` /\ `k2 <= n` /\ `x2 = (F k2)` /\
                          `y2 = (F k2 - 1)` /\ `k2 >= n` k1 x1 y1 result4
                          Post8) end) `n - result` result result0 result1
                    (refl_equal ? `n - result`)
                    (fib3_po_6 n Pre4 result Post1 result0 Post2 result1
                    Post3 Test4)) in
                (exist_4 [k1: Z][x1: Z][y1: Z][result4: unit]`x1 = (F n)` 
                k0 x0 y0 result3
                (fib3_po_7 n Pre4 result Post1 result0 Post2 result1 Post3
                Test4 k0 x0 y0 Post8))
            | (right Test1) =>
                let (result3, Post16) = (exist_1 [result3: unit]
                  `result0 = (F n)` tt
                  (fib3_po_8 n Pre4 result Post1 result0 Post2 result1 Post3
                  Test1)) in
                (exist_4 [k0: Z][x0: Z][y0: Z][result4: unit]
                `x0 = (F n)` result result0 result1 result3 Post16) end) in
          let (result3, Post18) = (exist_1 [result3: Z]`result3 = (F n)` 
            x0 Post14) in
          (exist_4 [k1: Z][x1: Z][y1: Z][result4: Z]`result4 = (F n)` 
          k0 x0 y0 result3 Post18) in
        (exist_3 [k1: Z][x1: Z][result3: Z]`result3 = (F n)` k0 x0 result2
        Post13) in
      (exist_2 [k1: Z][result2: Z]`result2 = (F n)` k0 result1 Post12) in
    (exist_1 [result1: Z]`result1 = (F n)` result0 Post11).

