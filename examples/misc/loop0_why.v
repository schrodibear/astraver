
Require Why.
Require Omega.

Lemma p_po_1 : 
  (x: Z)
  (Pre4: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = x0)
  (Pre2: `0 <= x0` /\ `x0 <= x`)
  (Test2: `x0 > 0`)
  (x1: Z)
  (Post1: x1 = `x0 - 1`)
  (`0 <= x1` /\ `x1 <= x`) /\ (Zwf `0` x1 x0).
Proof. 
Intros; Unfold Zwf; Intuition.
Save.

Lemma p_po_2 : 
  (x: Z)
  (Pre4: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = x0)
  (Pre2: `0 <= x0` /\ `x0 <= x`)
  (Test1: `x0 <= 0`)
  `x0 = 0`.
Proof.
Intuition.
Save.

Lemma p_po_3 : 
  (x: Z)
  (Pre4: `x >= 0`)
  `0 <= x` /\ `x <= x`.
Proof.
Intuition.
Save.

Definition p := (* validation *)
  [x: Z; Pre4: `x >= 0`]
    (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`) [Variant1: Z]
      (x0: Z)(_: Variant1 = x0)(_0: `0 <= x0` /\ `x0 <= x`)
      (sig_2 Z unit [x1: Z][result: unit](`x1 = 0`))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (x0: Z)(_: Variant2 = x0)(_0: `0 <= x0` /\ `x0 <= x`)
       (sig_2 Z unit [x1: Z][result: unit](`x1 = 0`)); x0: Z;
       Pre3: Variant1 = x0; Pre2: `0 <= x0` /\ `x0 <= x`]
        let (result, Bool1) =
          let (result1, Post3) = (Z_gt_le_bool x0 `0`) in
          (exist_1 [result2: bool]
          (if result2 then `x0 > 0` else `x0 <= 0`) result1 Post3) in
        (Cases (btest [result:bool](if result then `x0 > 0` else `x0 <= 0`)
                result Bool1) of
        | (left Test2) =>
            let (x1, result0, Post5) =
              let (x1, result0, Post2) =
                let (x1, result0, Post1) =
                  let (result0, Post1) = (exist_1 [result0: Z]
                    result0 = `x0 - 1` `x0 - 1` (refl_equal ? `x0 - 1`)) in
                  (exist_2 [x2: Z][result1: unit]x2 = `x0 - 1` result0 
                  tt Post1) in
                (exist_2 [x2: Z][result1: unit](`0 <= x2` /\ `x2 <= x`) /\
                (Zwf `0` x2 x0) x1 result0
                (p_po_1 x Pre4 Variant1 x0 Pre3 Pre2 Test2 x1 Post1)) in
              ((wf1 x1) (loop_variant_1 Pre3 Post2) x1 (refl_equal ? x1)
                (proj1 ? ? Post2)) in
            (exist_2 [x2: Z][result1: unit]`x2 = 0` x1 result0 Post5)
        | (right Test1) =>
            let (x1, result0, Post4) = (exist_2 [x1: Z][result0: unit]
              `x1 = 0` x0 tt (p_po_2 x Pre4 Variant1 x0 Pre3 Pre2 Test1)) in
            (exist_2 [x2: Z][result1: unit]`x2 = 0` x1 result0 Post4) end) 
      x x (refl_equal ? x) (p_po_3 x Pre4)).

