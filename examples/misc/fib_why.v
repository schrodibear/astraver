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
  (Variant1: Z)
  (n0: Z)
  (Pre7: Variant1 = n0)
  (Pre6: `n0 >= 0`)
  (Test2: `n0 <= 1`)
  `1 = (F n0)`.
Proof.
Intros.
Assert `n0 = 0` \/ `n0 = 1`; 
Intuition Try (Rewrite H0; Auto with *).
Omega.
Save.

Lemma fib1_po_2 : 
  (n: Z)
  (Pre8: `n >= 0`)
  (Variant1: Z)
  (n0: Z)
  (Pre7: Variant1 = n0)
  (Pre6: `n0 >= 0`)
  (Test1: `n0 > 1`)
  `n0 - 2 >= 0`.
Proof.
Intros; Omega.
Save.

Lemma fib1_po_3 : 
  (n: Z)
  (Pre8: `n >= 0`)
  (Variant1: Z)
  (n0: Z)
  (Pre7: Variant1 = n0)
  (Pre6: `n0 >= 0`)
  (Test1: `n0 > 1`)
  (Pre3: `n0 - 2 >= 0`)
  (Zwf `0` `n0 - 2` Variant1).
Proof.
Intros; Unfold Zwf; Omega.
Save.

Lemma fib1_po_4 : 
  (n: Z)
  (Pre8: `n >= 0`)
  (Variant1: Z)
  (n0: Z)
  (Pre7: Variant1 = n0)
  (Pre6: `n0 >= 0`)
  (Test1: `n0 > 1`)
  (aux_4: Z)
  (Post4: `aux_4 = (F n0 - 2)`)
  `n0 - 1 >= 0`.
Proof.
Intros; Omega.
Save.

Lemma fib1_po_5 : 
  (n: Z)
  (Pre8: `n >= 0`)
  (Variant1: Z)
  (n0: Z)
  (Pre7: Variant1 = n0)
  (Pre6: `n0 >= 0`)
  (Test1: `n0 > 1`)
  (aux_4: Z)
  (Post4: `aux_4 = (F n0 - 2)`)
  (Pre5: `n0 - 1 >= 0`)
  (Zwf `0` `n0 - 1` Variant1).
Proof.
Intros; Unfold Zwf; Omega.
Save.

Lemma fib1_po_6 : 
  (n: Z)
  (Pre8: `n >= 0`)
  (Variant1: Z)
  (n0: Z)
  (Pre7: Variant1 = n0)
  (Pre6: `n0 >= 0`)
  (Test1: `n0 > 1`)
  (aux_4: Z)
  (Post4: `aux_4 = (F n0 - 2)`)
  (aux_3: Z)
  (Post7: `aux_3 = (F n0 - 1)`)
  `aux_3 + aux_4 = (F n0)`.
Proof.
Intros.
Subst aux_4 aux_3.
Symmetry; Auto with *.
Save.

Definition fib1 := (* validation *)
  [n: Z; Pre8: `n >= 0`]
    (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`) [Variant1: Z]
      (n0: Z)(_: Variant1 = n0)(_0: `n0 >= 0`)
      (sig_1 Z [result: Z](`result = (F n0)`))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (n0: Z)(_: Variant2 = n0)(_0: `n0 >= 0`)
       (sig_1 Z [result: Z](`result = (F n0)`)); n0: Z; Pre7: Variant1 = n0;
       Pre6: `n0 >= 0`]
        let (result, Bool2) =
          let (result1, Post2) = (Z_le_gt_bool n0 `1`) in
          (exist_1 [result2: bool]
          (if result2 then `n0 <= 1` else `n0 > 1`) result1 Post2) in
        (Cases (btest [result:bool](if result then `n0 <= 1` else `n0 > 1`)
                result Bool2) of
        | (left Test2) =>
            let (result0, Post10) = (exist_1 [result0: Z]
              `result0 = (F n0)` `1`
              (fib1_po_1 n Pre8 Variant1 n0 Pre7 Pre6 Test2)) in
            (exist_1 [result1: Z]`result1 = (F n0)` result0 Post10)
        | (right Test1) =>
            let (result0, Post3) =
              let (aux_4, Post4) =
                let Pre3 = (fib1_po_2 n Pre8 Variant1 n0 Pre7 Pre6 Test1) in
                let (result2, Post5) =
                  ((wf1 `n0 - 2`)
                    (fib1_po_3 n Pre8 Variant1 n0 Pre7 Pre6 Test1 Pre3)
                    `n0 - 2` (refl_equal ? `n0 - 2`) Pre3) in
                (exist_1 [result3: Z]`result3 = (F n0 - 2)` result2 Post5) in
              let (result0, Post6) =
                let (aux_3, Post7) =
                  let Pre5 =
                    (fib1_po_4 n Pre8 Variant1 n0 Pre7 Pre6 Test1 aux_4
                    Post4) in
                  let (result2, Post8) =
                    ((wf1 `n0 - 1`)
                      (fib1_po_5 n Pre8 Variant1 n0 Pre7 Pre6 Test1 aux_4
                      Post4 Pre5) `n0 - 1` (refl_equal ? `n0 - 1`) Pre5) in
                  (exist_1 [result3: Z]`result3 = (F n0 - 1)` result2 Post8) in
                let (result0, Post9) = (exist_1 [result0: Z]
                  `result0 = (F n0)` `aux_3 + aux_4`
                  (fib1_po_6 n Pre8 Variant1 n0 Pre7 Pre6 Test1 aux_4 Post4
                  aux_3 Post7)) in
                (exist_1 [result1: Z]`result1 = (F n0)` result0 Post9) in
              (exist_1 [result1: Z]`result1 = (F n0)` result0 Post6) in
            (exist_1 [result1: Z]`result1 = (F n0)` result0 Post3) end) 
      n n (refl_equal ? n) Pre8).

Lemma fib2_aux_po_1 : 
  (n: Z)
  (x: Z)
  (fx: Z)
  (fx_1: Z)
  (Pre6: (`1 <= x` /\ `x <= n`) /\ `fx = (F x)` /\ `fx_1 = (F x - 1)`)
  (Variant1: Z)
  (n0: Z)
  (x0: Z)
  (fx0: Z)
  (fx_2: Z)
  (Pre5: Variant1 = `n0 - x0`)
  (Pre4: (`1 <= x0` /\ `x0 <= n0`) /\ `fx0 = (F x0)` /\ `fx_2 = (F x0 - 1)`)
  (Test2: `x0 = n0`)
  `fx0 = (F n0)`.
Proof.
Intuition.
Rewrite <- Test2; Assumption.
Save.

Lemma fib2_aux_po_2 : 
  (n: Z)
  (x: Z)
  (fx: Z)
  (fx_1: Z)
  (Pre6: (`1 <= x` /\ `x <= n`) /\ `fx = (F x)` /\ `fx_1 = (F x - 1)`)
  (Variant1: Z)
  (n0: Z)
  (x0: Z)
  (fx0: Z)
  (fx_2: Z)
  (Pre5: Variant1 = `n0 - x0`)
  (Pre4: (`1 <= x0` /\ `x0 <= n0`) /\ `fx0 = (F x0)` /\ `fx_2 = (F x0 - 1)`)
  (Test1: `x0 <> n0`)
  (`1 <= x0 + 1` /\ `x0 + 1 <= n0`) /\ `fx0 + fx_2 = (F x0 + 1)` /\
  `fx0 = (F x0 + 1 - 1)`.
Proof.
Intuition.
Subst fx0 fx_2; Symmetry.
Generalize H5. Replace x0 with `(x0+1)-1`. Generalize `x0+1`.
Intros; Ring `z-1+1`; Replace `z-1-1` with `z-2`. 
Auto with *.
Omega.
Omega.
Ring `x0+1-1`; Trivial.
Save.

Lemma fib2_aux_po_3 : 
  (n: Z)
  (x: Z)
  (fx: Z)
  (fx_1: Z)
  (Pre6: (`1 <= x` /\ `x <= n`) /\ `fx = (F x)` /\ `fx_1 = (F x - 1)`)
  (Variant1: Z)
  (n0: Z)
  (x0: Z)
  (fx0: Z)
  (fx_2: Z)
  (Pre5: Variant1 = `n0 - x0`)
  (Pre4: (`1 <= x0` /\ `x0 <= n0`) /\ `fx0 = (F x0)` /\ `fx_2 = (F x0 - 1)`)
  (Test1: `x0 <> n0`)
  (Pre3: (`1 <= x0 + 1` /\ `x0 + 1 <= n0`) /\ `fx0 + fx_2 = (F x0 + 1)` /\
         `fx0 = (F x0 + 1 - 1)`)
  (Zwf `0` `n0 - (x0 + 1)` Variant1).
Proof.
Intuition.
Unfold Zwf; Omega.
Save.

Definition fib2_aux := (* validation *)
  [n: Z; x: Z; fx: Z; fx_1: Z; Pre6: (`1 <= x` /\ `x <= n`) /\
   `fx = (F x)` /\ `fx_1 = (F x - 1)`]
    (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`) [Variant1: Z]
      (n0: Z)(x0: Z)(fx0: Z)(fx_2: Z)(_: Variant1 = `n0 - x0`)
      (_0: (`1 <= x0` /\ `x0 <= n0`) /\ `fx0 = (F x0)` /\
      `fx_2 = (F x0 - 1)`)(sig_1 Z [result: Z](`result = (F n0)`))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (n0: Z)(x0: Z)(fx0: Z)(fx_2: Z)(_: Variant2 = `n0 - x0`)
       (_0: (`1 <= x0` /\ `x0 <= n0`) /\ `fx0 = (F x0)` /\
       `fx_2 = (F x0 - 1)`)(sig_1 Z [result: Z](`result = (F n0)`)); n0: Z;
       x0: Z; fx0: Z; fx_2: Z; Pre5: Variant1 = `n0 - x0`;
       Pre4: (`1 <= x0` /\ `x0 <= n0`) /\ `fx0 = (F x0)` /\
       `fx_2 = (F x0 - 1)`]
        let (result, Bool2) =
          let (result1, Post2) = (Z_eq_bool x0 n0) in
          (exist_1 [result2: bool]
          (if result2 then `x0 = n0` else `x0 <> n0`) result1 Post2) in
        (Cases (btest [result:bool](if result then `x0 = n0` else `x0 <> n0`)
                result Bool2) of
        | (left Test2) =>
            let (result0, Post5) = (exist_1 [result0: Z]
              `result0 = (F n0)` fx0
              (fib2_aux_po_1 n x fx fx_1 Pre6 Variant1 n0 x0 fx0 fx_2 Pre5
              Pre4 Test2)) in
            (exist_1 [result1: Z]`result1 = (F n0)` result0 Post5)
        | (right Test1) =>
            let (result0, Post3) =
              let Pre3 =
                (fib2_aux_po_2 n x fx fx_1 Pre6 Variant1 n0 x0 fx0 fx_2 Pre5
                Pre4 Test1) in
              let (result2, Post4) =
                ((wf1 `n0 - (x0 + 1)`)
                  (fib2_aux_po_3 n x fx fx_1 Pre6 Variant1 n0 x0 fx0 fx_2
                  Pre5 Pre4 Test1 Pre3) n0 `x0 + 1` `fx0 + fx_2` fx0
                  (refl_equal ? `n0 - (x0 + 1)`) Pre3) in
              (exist_1 [result3: Z]`result3 = (F n0)` result2 Post4) in
            (exist_1 [result1: Z]`result1 = (F n0)` result0 Post3) end)
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
  (`1 <= 1` /\ `1 <= n`) /\ `1 = (F 1)` /\ `1 = (F 1 - 1)`.
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
  (Post8: result = `1`)
  (result0: Z)
  (Post7: result0 = `1`)
  (result1: Z)
  (Post6: result1 = `1`)
  (Test4: `n > 0`)
  (Variant1: Z)
  (k0: Z)
  (x0: Z)
  (y0: Z)
  (Pre3: Variant1 = `n - k0`)
  (Pre2: (`1 <= k0` /\ `k0 <= n`) /\ `x0 = (F k0)` /\ `y0 = (F k0 - 1)`)
  (Test3: `k0 < n`)
  (t: Z)
  (Post4: t = y0)
  (y1: Z)
  (Post1: y1 = x0)
  (x1: Z)
  (Post2: x1 = `x0 + t`)
  (k1: Z)
  (Post3: k1 = `k0 + 1`)
  ((`1 <= k1` /\ `k1 <= n`) /\ `x1 = (F k1)` /\ `y1 = (F k1 - 1)`) /\
  (Zwf `0` `n - k1` `n - k0`).
Proof.
Intuition.
Subst k1; Subst x1; Subst t.
Subst x0 y0.
Symmetry.
Generalize H1. Replace k0 with `(k0+1)-1`. Generalize `k0+1`.
Intros; Ring `z-1+1`; Replace `z-1-1` with `z-2`. 
Auto with *.
Omega.
Omega.
Subst k1; Ring `k0+1-1`; Trivial.
Subst y1; Assumption.
Unfold Zwf; Omega.
Save.

Lemma fib3_po_2 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (result: Z)
  (Post8: result = `1`)
  (result0: Z)
  (Post7: result0 = `1`)
  (result1: Z)
  (Post6: result1 = `1`)
  (Test4: `n > 0`)
  (Variant1: Z)
  (k0: Z)
  (x0: Z)
  (y0: Z)
  (Pre3: Variant1 = `n - k0`)
  (Pre2: (`1 <= k0` /\ `k0 <= n`) /\ `x0 = (F k0)` /\ `y0 = (F k0 - 1)`)
  (Test3: `k0 < n`)
  (k1: Z)
  (x1: Z)
  (y1: Z)
  (Post9: ((`1 <= k1` /\ `k1 <= n`) /\ `x1 = (F k1)` /\ `y1 = (F k1 - 1)`) /\
          (Zwf `0` `n - k1` `n - k0`))
  (Zwf `0` `n - k1` Variant1).
Proof.
Intuition.
Rewrite Pre3; Assumption.
Save.

Lemma fib3_po_3 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (result: Z)
  (Post8: result = `1`)
  (result0: Z)
  (Post7: result0 = `1`)
  (result1: Z)
  (Post6: result1 = `1`)
  (Test4: `n > 0`)
  (`1 <= result` /\ `result <= n`) /\ `result0 = (F result)` /\
  `result1 = (F result - 1)`.
Proof.
Intuition.
Subst result result0.
Auto with *.
Subst result result1.
Auto with *.
Save.

Lemma fib3_po_4 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (result: Z)
  (Post8: result = `1`)
  (result0: Z)
  (Post7: result0 = `1`)
  (result1: Z)
  (Post6: result1 = `1`)
  (Test4: `n > 0`)
  (k0: Z)
  (x0: Z)
  (y0: Z)
  (Post5: ((`1 <= k0` /\ `k0 <= n`) /\ `x0 = (F k0)` /\ `y0 = (F k0 - 1)`) /\
          `k0 >= n`)
  `x0 = (F n)`.
Proof.
Intuition.
Replace n with k0. Auto. Omega.
Save.

Lemma fib3_po_5 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (result: Z)
  (Post8: result = `1`)
  (result0: Z)
  (Post7: result0 = `1`)
  (result1: Z)
  (Post6: result1 = `1`)
  (Test1: `n <= 0`)
  `result0 = (F n)`.
Proof.
Intuition.
Subst result0. Replace n  with `0`. Auto.
Omega.
Save.

Definition fib3 := (* validation *)
  [n: Z; Pre4: `n >= 0`]
    let (result, Post8) = (exist_1 [result: Z]result = `1` `1`
      (refl_equal ? `1`)) in
    let (k0, result0, Post11) =
      let (result0, Post7) = (exist_1 [result0: Z]result0 = `1` `1`
        (refl_equal ? `1`)) in
      let (k0, x0, result1, Post12) =
        let (result1, Post6) = (exist_1 [result1: Z]result1 = `1` `1`
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
                let (k0, x0, y0, result3, Post5) =
                  (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `
                    0`) [Variant1: Z](k0: Z)(x0: Z)(y0: Z)
                    (_: Variant1 = `n - k0`)(_0: (`1 <= k0` /\ `k0 <= n`) /\
                    `x0 = (F k0)` /\ `y0 = (F k0 - 1)`)
                    (sig_4 Z Z Z unit [k1: Z][x1: Z][y1: Z][result3: unit]
                     (((`1 <= k1` /\ `k1 <= n`) /\ `x1 = (F k1)` /\
                     `y1 = (F k1 - 1)`) /\ `k1 >= n`))
                    [Variant1: Z; wf1: (Variant2: Z)
                     (Pre1: (Zwf `0` Variant2 Variant1))(k0: Z)(x0: Z)(y0: Z)
                     (_: Variant2 = `n - k0`)(_0: (`1 <= k0` /\ `k0 <= n`) /\
                     `x0 = (F k0)` /\ `y0 = (F k0 - 1)`)
                     (sig_4 Z Z Z unit [k1: Z][x1: Z][y1: Z][result3: unit]
                      (((`1 <= k1` /\ `k1 <= n`) /\ `x1 = (F k1)` /\
                      `y1 = (F k1 - 1)`) /\ `k1 >= n`));
                     k0: Z; x0: Z; y0: Z; Pre3: Variant1 = `n - k0`;
                     Pre2: (`1 <= k0` /\ `k0 <= n`) /\ `x0 = (F k0)` /\
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
                          let (k1, x1, y1, result4, Post5) =
                            let (k1, x1, y1, result4, Post9) =
                              let (k1, x1, y1, result4, Post9) =
                                let (t, Post4) = (exist_1 [result4: Z]
                                  result4 = y0 y0 (refl_equal ? y0)) in
                                let (k1, x1, y1, result4, Post9) =
                                  let (y1, result4, Post1) =
                                    let (result4, Post1) =
                                      (exist_1 [result4: Z]result4 = x0 
                                      x0 (refl_equal ? x0)) in
                                    (exist_2 [y2: Z][result5: unit]
                                    y2 = x0 result4 tt Post1) in
                                  let (x1, result5, Post2) =
                                    let (result5, Post2) =
                                      (exist_1 [result5: Z]
                                      result5 = `x0 + t` `x0 + t`
                                      (refl_equal ? `x0 + t`)) in
                                    (exist_2 [x2: Z][result6: unit]
                                    x2 = `x0 + t` result5 tt Post2) in
                                  let (k1, result6, Post3) =
                                    let (result6, Post3) =
                                      (exist_1 [result6: Z]
                                      result6 = `k0 + 1` `k0 + 1`
                                      (refl_equal ? `k0 + 1`)) in
                                    (exist_2 [k2: Z][result7: unit]
                                    k2 = `k0 + 1` result6 tt Post3) in
                                  (exist_4 [k2: Z][x2: Z][y2: Z]
                                  [result7: unit]((`1 <= k2` /\ `k2 <= n`) /\
                                  `x2 = (F k2)` /\ `y2 = (F k2 - 1)`) /\
                                  (Zwf `0` `n - k2` `n - k0`) k1 x1 y1
                                  result6
                                  (fib3_po_1 n Pre4 result Post8 result0
                                  Post7 result1 Post6 Test4 Variant1 k0 x0 y0
                                  Pre3 Pre2 Test3 t Post4 y1 Post1 x1 Post2
                                  k1 Post3)) in
                                (exist_4 [k2: Z][x2: Z][y2: Z][result5: unit]
                                ((`1 <= k2` /\ `k2 <= n`) /\ `x2 = (F k2)` /\
                                `y2 = (F k2 - 1)`) /\
                                (Zwf `0` `n - k2` `n - k0`) k1 x1 y1 
                                result4 Post9) in
                              (exist_4 [k2: Z][x2: Z][y2: Z][result5: unit]
                              ((`1 <= k2` /\ `k2 <= n`) /\ `x2 = (F k2)` /\
                              `y2 = (F k2 - 1)`) /\
                              (Zwf `0` `n - k2` `n - k0`) k1 x1 y1 result4
                              Post9) in
                            ((wf1 `n - k1`)
                              (fib3_po_2 n Pre4 result Post8 result0 Post7
                              result1 Post6 Test4 Variant1 k0 x0 y0 Pre3 Pre2
                              Test3 k1 x1 y1 Post9) k1 x1 y1
                              (refl_equal ? `n - k1`) (proj1 ? ? Post9)) in
                          (exist_4 [k2: Z][x2: Z][y2: Z][result5: unit]
                          ((`1 <= k2` /\ `k2 <= n`) /\ `x2 = (F k2)` /\
                          `y2 = (F k2 - 1)`) /\ `k2 >= n` k1 x1 y1 result4
                          Post5)
                      | (right Test2) =>
                          let (k1, x1, y1, result4, Post5) = (exist_4 [k1: Z]
                            [x1: Z][y1: Z][result4: unit]((`1 <= k1` /\
                            `k1 <= n`) /\ `x1 = (F k1)` /\
                            `y1 = (F k1 - 1)`) /\ `k1 >= n` k0 x0 y0 
                            tt (conj ? ? Pre2 Test2)) in
                          (exist_4 [k2: Z][x2: Z][y2: Z][result5: unit]
                          ((`1 <= k2` /\ `k2 <= n`) /\ `x2 = (F k2)` /\
                          `y2 = (F k2 - 1)`) /\ `k2 >= n` k1 x1 y1 result4
                          Post5) end) `n - result` result result0 result1
                    (refl_equal ? `n - result`)
                    (fib3_po_3 n Pre4 result Post8 result0 Post7 result1
                    Post6 Test4)) in
                (exist_4 [k1: Z][x1: Z][y1: Z][result4: unit]`x1 = (F n)` 
                k0 x0 y0 result3
                (fib3_po_4 n Pre4 result Post8 result0 Post7 result1 Post6
                Test4 k0 x0 y0 Post5))
            | (right Test1) =>
                let (result3, Post16) = (exist_1 [result3: unit]
                  `result0 = (F n)` tt
                  (fib3_po_5 n Pre4 result Post8 result0 Post7 result1 Post6
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

(*Why*) Parameter N : Z.

Lemma fib4_po_1 : 
  (n: Z)
  (Pre10: `0 <= n` /\ `n < N`)
  (Test4: `n <= 1`)
  `1 = (F n)`.
Proof.
Intros.
Assert h: `n=0` \/ `n=1`. Omega.
Intuition; Rewrite H1; Auto.
Save.

Lemma fib4_po_2 : 
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= n` /\ `n < N`)
  (Test3: `n > 1`)
  (result0: Z)
  (Post1: (store t `0` result0) = (store t `0` `1`))
  `0 <= 0` /\ `0 < N`.
Proof.
Intros; Omega.
Save.

Lemma fib4_po_3 : 
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= n` /\ `n < N`)
  (Test3: `n > 1`)
  (t0: (array N Z))
  (Post1: t0 = (store t `0` `1`))
  (result1: Z)
  (Post2: (store t0 `1` result1) = (store t0 `1` `1`))
  `0 <= 1` /\ `1 < N`.
Proof.
Intros; Omega.
Save.

Lemma fib4_po_4 : 
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= n` /\ `n < N`)
  (Test3: `n > 1`)
  (t0: (array N Z))
  (Post1: t0 = (store t `0` `1`))
  (t1: (array N Z))
  (Post2: t1 = (store t0 `1` `1`))
  (result2: Z)
  (Post6: result2 = `2`)
  (Variant1: Z)
  (k0: Z)
  (t2: (array N Z))
  (Pre8: Variant1 = `n + 1 - k0`)
  (Pre7: (`2 <= k0` /\ `k0 <= n + 1`) /\
         ((i:Z) (`0 <= i` /\ `i < k0` -> `(access t2 i) = (F i)`)))
  (Test2: `k0 <= n`)
  `0 <= k0 - 2` /\ `k0 - 2 < N`.
Proof.
Intros; Omega.
Save.

Lemma fib4_po_5 : 
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= n` /\ `n < N`)
  (Test3: `n > 1`)
  (t0: (array N Z))
  (Post1: t0 = (store t `0` `1`))
  (t1: (array N Z))
  (Post2: t1 = (store t0 `1` `1`))
  (result2: Z)
  (Post6: result2 = `2`)
  (Variant1: Z)
  (k0: Z)
  (t2: (array N Z))
  (Pre8: Variant1 = `n + 1 - k0`)
  (Pre7: (`2 <= k0` /\ `k0 <= n + 1`) /\
         ((i:Z) (`0 <= i` /\ `i < k0` -> `(access t2 i) = (F i)`)))
  (Test2: `k0 <= n`)
  (Pre4: `0 <= k0 - 2` /\ `k0 - 2 < N`)
  `0 <= k0 - 1` /\ `k0 - 1 < N`.
Proof.
Intros; Omega.
Save.

Lemma fib4_po_6 : 
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= n` /\ `n < N`)
  (Test3: `n > 1`)
  (t0: (array N Z))
  (Post1: t0 = (store t `0` `1`))
  (t1: (array N Z))
  (Post2: t1 = (store t0 `1` `1`))
  (result2: Z)
  (Post6: result2 = `2`)
  (Variant1: Z)
  (k0: Z)
  (t2: (array N Z))
  (Pre8: Variant1 = `n + 1 - k0`)
  (Pre7: (`2 <= k0` /\ `k0 <= n + 1`) /\
         ((i:Z) (`0 <= i` /\ `i < k0` -> `(access t2 i) = (F i)`)))
  (Test2: `k0 <= n`)
  (Pre4: `0 <= k0 - 2` /\ `k0 - 2 < N`)
  (Pre5: `0 <= k0 - 1` /\ `k0 - 1 < N`)
  (result4: Z)
  (Post3: (store t2 k0 result4) = (store t2 k0
                                   `(access t2 k0 - 1) + (access t2 k0 - 2)`))
  `0 <= k0` /\ `k0 < N`.
Proof.
Intros; Omega.
Save.

Lemma fib4_po_7 : 
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= n` /\ `n < N`)
  (Test3: `n > 1`)
  (t0: (array N Z))
  (Post1: t0 = (store t `0` `1`))
  (t1: (array N Z))
  (Post2: t1 = (store t0 `1` `1`))
  (result2: Z)
  (Post6: result2 = `2`)
  (Variant1: Z)
  (k0: Z)
  (t2: (array N Z))
  (Pre8: Variant1 = `n + 1 - k0`)
  (Pre7: (`2 <= k0` /\ `k0 <= n + 1`) /\
         ((i:Z) (`0 <= i` /\ `i < k0` -> `(access t2 i) = (F i)`)))
  (Test2: `k0 <= n`)
  (Pre4: `0 <= k0 - 2` /\ `k0 - 2 < N`)
  (Pre5: `0 <= k0 - 1` /\ `k0 - 1 < N`)
  (t3: (array N Z))
  (Post3: t3 = (store t2 k0 `(access t2 k0 - 1) + (access t2 k0 - 2)`))
  (k1: Z)
  (Post4: k1 = `k0 + 1`)
  ((`2 <= k1` /\ `k1 <= n + 1`) /\
  ((i:Z) (`0 <= i` /\ `i < k1` -> `(access t3 i) = (F i)`))) /\
  (Zwf `0` `n + 1 - k1` `n + 1 - k0`).
Proof.
Intuition.
Subst t3.
Assert hi : `i=k0` \/ `i<k0`. Omega.
Intuition.
Subst i. Rewrite store_def_1.
Rewrite (H2 `k0-1`). 
Rewrite (H2 `k0-2`). 
Symmetry; Auto with *.
Omega.
Omega.
Omega.
Rewrite store_def_2.
Auto.
Omega.
Omega.
Omega.
Unfold Zwf; Omega.
Save.

Lemma fib4_po_8 : 
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= n` /\ `n < N`)
  (Test3: `n > 1`)
  (t0: (array N Z))
  (Post1: t0 = (store t `0` `1`))
  (t1: (array N Z))
  (Post2: t1 = (store t0 `1` `1`))
  (result2: Z)
  (Post6: result2 = `2`)
  (Variant1: Z)
  (k0: Z)
  (t2: (array N Z))
  (Pre8: Variant1 = `n + 1 - k0`)
  (Pre7: (`2 <= k0` /\ `k0 <= n + 1`) /\
         ((i:Z) (`0 <= i` /\ `i < k0` -> `(access t2 i) = (F i)`)))
  (Test2: `k0 <= n`)
  (k1: Z)
  (t3: (array N Z))
  (Post7: ((`2 <= k1` /\ `k1 <= n + 1`) /\
          ((i:Z) (`0 <= i` /\ `i < k1` -> `(access t3 i) = (F i)`))) /\
          (Zwf `0` `n + 1 - k1` `n + 1 - k0`))
  (Zwf `0` `n + 1 - k1` Variant1).
Proof.
Intuition.
Rewrite Pre8; Assumption.
Save.

Lemma fib4_po_9 : 
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= n` /\ `n < N`)
  (Test3: `n > 1`)
  (t0: (array N Z))
  (Post1: t0 = (store t `0` `1`))
  (t1: (array N Z))
  (Post2: t1 = (store t0 `1` `1`))
  (result2: Z)
  (Post6: result2 = `2`)
  (`2 <= result2` /\ `result2 <= n + 1`) /\
  ((i:Z) (`0 <= i` /\ `i < result2` -> `(access t1 i) = (F i)`)).
Proof.
Intuition.
Assert hi: `i=0` \/ `i=1`. Omega. Intuition.
Subst i t1; Rewrite store_def_2; Try Omega.
Subst t0; Rewrite store_def_1; Try Omega. Auto.
Subst i t1; Rewrite store_def_1; Try Omega. Auto.
Save.

Lemma fib4_po_10 : 
  (n: Z)
  (t: (array N Z))
  (Pre10: `0 <= n` /\ `n < N`)
  (Test3: `n > 1`)
  (t0: (array N Z))
  (Post1: t0 = (store t `0` `1`))
  (t1: (array N Z))
  (Post2: t1 = (store t0 `1` `1`))
  (result2: Z)
  (Post6: result2 = `2`)
  (k0: Z)
  (t2: (array N Z))
  (Post5: ((`2 <= k0` /\ `k0 <= n + 1`) /\
          ((i:Z) (`0 <= i` /\ `i < k0` -> `(access t2 i) = (F i)`))) /\
          `k0 > n`)
  `(access t2 n) = (F n)`.
Proof.
Intuition.
Save.

Definition fib4 := (* validation *)
  [n: Z; t: (array N Z); Pre10: `0 <= n` /\ `n < N`]
    let (result, Bool2) =
      let (result1, Post9) = (Z_le_gt_bool n `1`) in
      (exist_1 [result2: bool](if result2 then `n <= 1` else `n > 1`) 
      result1 Post9) in
    (Cases (btest [result:bool](if result then `n <= 1` else `n > 1`) result
            Bool2) of
    | (left Test4) =>
        let (result0, Post14) = (exist_1 [result0: Z]`result0 = (F n)` 
          `1` (fib4_po_1 n Pre10 Test4)) in
        (exist_2 [t0: (array N Z)][result1: Z]`result1 = (F n)` t result0
        Post14)
    | (right Test3) =>
        let (t0, result0, Post10) =
          let (t0, result0, Post1) =
            let (result0, Post1) = (exist_1 [result0: Z]
              (store t `0` result0) = (store t `0` `1`) `1`
              (refl_equal ? (store t `0` `1`))) in
            let Pre1 = (fib4_po_2 n t Pre10 Test3 result0 Post1) in
            (exist_2 [t1: (array N Z)][result2: unit]
            t1 = (store t `0` `1`) (store t `0` result0) tt Post1) in
          let (t1, result1, Post2) =
            let (result1, Post2) = (exist_1 [result1: Z]
              (store t0 `1` result1) = (store t0 `1` `1`) `1`
              (refl_equal ? (store t0 `1` `1`))) in
            let Pre2 = (fib4_po_3 n t Pre10 Test3 t0 Post1 result1 Post2) in
            (exist_2 [t2: (array N Z)][result3: unit]
            t2 = (store t0 `1` `1`) (store t0 `1` result1) tt Post2) in
          let (t2, result2, Post11) =
            let (result2, Post6) = (exist_1 [result2: Z]result2 = `2` 
              `2` (refl_equal ? `2`)) in
            let (k0, t2, result3, Post5) =
              (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `
                0`) [Variant1: Z](k0: Z)(t2: (array N Z))
                (_: Variant1 = `n + 1 - k0`)(_0: (`2 <= k0` /\
                `k0 <= n + 1`) /\
                ((i:Z) (`0 <= i` /\ `i < k0` -> `(access t2 i) = (F i)`)))
                (sig_3 Z (array N Z) unit [k1: Z][t3: (array N Z)]
                 [result3: unit](((`2 <= k1` /\ `k1 <= n + 1`) /\
                 ((i:Z) (`0 <= i` /\ `i < k1` -> `(access t3 i) = (F i)`))) /\
                 `k1 > n`))
                [Variant1: Z; wf1: (Variant2: Z)
                 (Pre3: (Zwf `0` Variant2 Variant1))(k0: Z)(t2: (array N Z))
                 (_: Variant2 = `n + 1 - k0`)(_0: (`2 <= k0` /\
                 `k0 <= n + 1`) /\
                 ((i:Z) (`0 <= i` /\ `i < k0` -> `(access t2 i) = (F i)`)))
                 (sig_3 Z (array N Z) unit [k1: Z][t3: (array N Z)]
                  [result3: unit](((`2 <= k1` /\ `k1 <= n + 1`) /\
                  ((i:Z) (`0 <= i` /\ `i < k1` -> `(access t3 i) = (F i)`))) /\
                  `k1 > n`));
                 k0: Z; t2: (array N Z); Pre8: Variant1 = `n + 1 - k0`;
                 Pre7: (`2 <= k0` /\ `k0 <= n + 1`) /\
                 ((i:Z) (`0 <= i` /\ `i < k0` -> `(access t2 i) = (F i)`))]
                  let (result3, Bool1) =
                    let (result5, Post12) = (Z_le_gt_bool k0 n) in
                    (exist_1 [result6: bool]
                    (if result6 then `k0 <= n` else `k0 > n`) result5 Post12) in
                  (Cases (btest
                          [result3:bool](if result3 then `k0 <= n`
                                         else `k0 > n`)
                          result3 Bool1) of
                  | (left Test2) =>
                      let (k1, t3, result4, Post5) =
                        let (k1, t3, result4, Post7) =
                          let Pre4 =
                            (fib4_po_4 n t Pre10 Test3 t0 Post1 t1 Post2
                            result2 Post6 Variant1 k0 t2 Pre8 Pre7 Test2) in
                          let Pre5 =
                            (fib4_po_5 n t Pre10 Test3 t0 Post1 t1 Post2
                            result2 Post6 Variant1 k0 t2 Pre8 Pre7 Test2
                            Pre4) in
                          let (t3, result4, Post3) =
                            let (result4, Post3) = (exist_1 [result4: Z]
                              (store t2 k0 result4) = (store t2 k0
                                                       `(access t2 k0 - 1) +
                                                        (access t2 k0 - 2)`) 
                              `(access t2 k0 - 1) + (access t2 k0 - 2)`
                              (refl_equal ? (store t2 k0
                                             `(access t2 k0 - 1) +
                                              (access t2 k0 - 2)`))) in
                            let Pre6 =
                              (fib4_po_6 n t Pre10 Test3 t0 Post1 t1 Post2
                              result2 Post6 Variant1 k0 t2 Pre8 Pre7 Test2
                              Pre4 Pre5 result4 Post3) in
                            (exist_2 [t4: (array N Z)][result6: unit]
                            t4 = (store t2 k0
                                  `(access t2 k0 - 1) + (access t2 k0 - 2)`) 
                            (store t2 k0 result4) tt Post3) in
                          let (k1, result5, Post4) =
                            let (result5, Post4) = (exist_1 [result5: Z]
                              result5 = `k0 + 1` `k0 + 1`
                              (refl_equal ? `k0 + 1`)) in
                            (exist_2 [k2: Z][result6: unit]
                            k2 = `k0 + 1` result5 tt Post4) in
                          (exist_3 [k2: Z][t4: (array N Z)][result6: unit]
                          ((`2 <= k2` /\ `k2 <= n + 1`) /\
                          ((i:Z)
                           (`0 <= i` /\ `i < k2` -> `(access t4 i) = (F i)`))) /\
                          (Zwf `0` `n + 1 - k2` `n + 1 - k0`) k1 t3 result5
                          (fib4_po_7 n t Pre10 Test3 t0 Post1 t1 Post2
                          result2 Post6 Variant1 k0 t2 Pre8 Pre7 Test2 Pre4
                          Pre5 t3 Post3 k1 Post4)) in
                        ((wf1 `n + 1 - k1`)
                          (fib4_po_8 n t Pre10 Test3 t0 Post1 t1 Post2
                          result2 Post6 Variant1 k0 t2 Pre8 Pre7 Test2 k1 t3
                          Post7) k1 t3 (refl_equal ? `n + 1 - k1`)
                          (proj1 ? ? Post7)) in
                      (exist_3 [k2: Z][t4: (array N Z)][result5: unit]
                      ((`2 <= k2` /\ `k2 <= n + 1`) /\
                      ((i:Z)
                       (`0 <= i` /\ `i < k2` -> `(access t4 i) = (F i)`))) /\
                      `k2 > n` k1 t3 result4 Post5)
                  | (right Test1) =>
                      let (k1, t3, result4, Post5) = (exist_3 [k1: Z]
                        [t3: (array N Z)][result4: unit]((`2 <= k1` /\
                        `k1 <= n + 1`) /\
                        ((i:Z)
                         (`0 <= i` /\ `i < k1` -> `(access t3 i) = (F i)`))) /\
                        `k1 > n` k0 t2 tt (conj ? ? Pre7 Test1)) in
                      (exist_3 [k2: Z][t4: (array N Z)][result5: unit]
                      ((`2 <= k2` /\ `k2 <= n + 1`) /\
                      ((i:Z)
                       (`0 <= i` /\ `i < k2` -> `(access t4 i) = (F i)`))) /\
                      `k2 > n` k1 t3 result4 Post5) end) `n + 1 - result2`
                result2 t1 (refl_equal ? `n + 1 - result2`)
                (fib4_po_9 n t Pre10 Test3 t0 Post1 t1 Post2 result2 Post6)) in
            (exist_2 [t3: (array N Z)][result4: unit]
            `(access t3 n) = (F n)` t2 result3
            (fib4_po_10 n t Pre10 Test3 t0 Post1 t1 Post2 result2 Post6 k0 t2
            Post5)) in
          let Pre9 = Pre10 in
          let (result3, Post13) = (exist_1 [result3: Z]
            `result3 = (F n)` (access t2 n) Post11) in
          (exist_2 [t3: (array N Z)][result4: Z]`result4 = (F n)` t2 
          result3 Post13) in
        (exist_2 [t1: (array N Z)][result1: Z]`result1 = (F n)` t0 result0
        Post10) end).

