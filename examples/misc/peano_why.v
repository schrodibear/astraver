
Require Why.
Require Omega.
Require ZArithRing.

Lemma add1_po_1 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post3: result = y)
  (Variant1: Z)
  (x0: Z)
  (z0: Z)
  (Pre2: Variant1 = z0)
  (I: `0 <= z0` /\ `x0 = x + (y - z0)`)
  (Test2: `z0 > 0`)
  (x1: Z)
  (Post1: x1 = `x0 + 1`)
  (z1: Z)
  (Post2: z1 = `z0 - 1`)
  (`0 <= z1` /\ `x1 = x + (y - z1)`) /\ (Zwf `0` z1 z0).
Proof. 
Unfold Zwf; Intros; Omega.
Save.

Lemma add1_po_2 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post3: result = y)
  `0 <= result` /\ `x = x + (y - result)`.
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma add1_po_3 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post3: result = y)
  (x0: Z)
  (z0: Z)
  (I: (`0 <= z0` /\ `x0 = x + (y - z0)`) /\ `z0 <= 0`)
  `x0 = x + y`.
Proof.
Intuition.
Save.

Definition add1 := (* validation *)
  [y: Z; x: Z; Pre3: `y >= 0`]
    let (result, Post3) = (exist_1 [result: Z]result = y y
      (refl_equal ? y)) in
    let (x0, z0, result0, I) =
      (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
        [Variant1: Z](x0: Z)(z0: Z)(_: Variant1 = z0)(I: `0 <= z0` /\
        `x0 = x + (y - z0)`)
        (sig_3 Z Z unit [x1: Z][z1: Z][result0: unit]((`0 <= z1` /\
         `x1 = x + (y - z1)`) /\ `z1 <= 0`))
        [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
         (x0: Z)(z0: Z)(_: Variant2 = z0)(I: `0 <= z0` /\
         `x0 = x + (y - z0)`)
         (sig_3 Z Z unit [x1: Z][z1: Z][result0: unit]((`0 <= z1` /\
          `x1 = x + (y - z1)`) /\ `z1 <= 0`));
         x0: Z; z0: Z; Pre2: Variant1 = z0; I: `0 <= z0` /\
         `x0 = x + (y - z0)`]
          let (result0, Bool1) =
            let (result2, Post4) = (Z_gt_le_bool z0 `0`) in
            (exist_1 [result3: bool]
            (if result3 then `z0 > 0` else `z0 <= 0`) result2 Post4) in
          (Cases (btest
                  [result0:bool](if result0 then `z0 > 0` else `z0 <= 0`)
                  result0 Bool1) of
          | (left Test2) =>
              let (x1, z1, result1, I0) =
                let (x1, z1, result1, I0) =
                  let (x1, result1, Post1) =
                    let (result1, Post1) = (exist_1 [result1: Z]
                      result1 = `x0 + 1` `x0 + 1` (refl_equal ? `x0 + 1`)) in
                    (exist_2 [x2: Z][result2: unit]x2 = `x0 + 1` result1 
                    tt Post1) in
                  let (z1, result2, Post2) =
                    let (result2, Post2) = (exist_1 [result2: Z]
                      result2 = `z0 - 1` `z0 - 1` (refl_equal ? `z0 - 1`)) in
                    (exist_2 [z2: Z][result3: unit]z2 = `z0 - 1` result2 
                    tt Post2) in
                  (exist_3 [x2: Z][z2: Z][result3: unit](`0 <= z2` /\
                  `x2 = x + (y - z2)`) /\ (Zwf `0` z2 z0) x1 z1 result2
                  (add1_po_1 y x Pre3 result Post3 Variant1 x0 z0 Pre2 I
                  Test2 x1 Post1 z1 Post2)) in
                ((wf1 z1) (loop_variant_1 Pre2 I0) x1 z1 (refl_equal ? z1)
                  (proj1 ? ? I0)) in
              (exist_3 [x2: Z][z2: Z][result2: unit](`0 <= z2` /\
              `x2 = x + (y - z2)`) /\ `z2 <= 0` x1 z1 result1 I0)
          | (right Test1) =>
              let (x1, z1, result1, I0) = (exist_3 [x1: Z][z1: Z]
                [result1: unit](`0 <= z1` /\ `x1 = x + (y - z1)`) /\
                `z1 <= 0` x0 z0 tt (conj ? ? I Test1)) in
              (exist_3 [x2: Z][z2: Z][result2: unit](`0 <= z2` /\
              `x2 = x + (y - z2)`) /\ `z2 <= 0` x1 z1 result1 I0) end) 
        result x result (refl_equal ? result)
        (add1_po_2 y x Pre3 result Post3)) in
    (exist_2 [x1: Z][result1: unit]`x1 = x + y` x0 result0
    (add1_po_3 y x Pre3 result Post3 x0 z0 I)).

Lemma u1_po_1 : 
  (result: Z)
  (Post1: result = `3`)
  `7 >= 0`.
Proof. Intros; Omega. Save.

Lemma u1_po_2 : 
  (result: Z)
  (Post1: result = `3`)
  (Pre1: `7 >= 0`)
  (r0: Z)
  (Post3: `r0 = result + 7`)
  `r0 = 10`.
Proof. Intros; Omega. Save.

Definition u1 := (* validation *)
  let (result, Post1) = (exist_1 [result: Z]result = `3` `3`
    (refl_equal ? `3`)) in
  let (r0, result0, Post2) =
    let Pre1 = (u1_po_1 result Post1) in
    let (r0, result2, Post3) = let Pre2 = Pre1 in
                               (add1 `7` result Pre2) in
    (exist_2 [r1: Z][result3: unit]`r1 = 10` r0 result2
    (u1_po_2 result Post1 Pre1 r0 Post3)) in
  result0.

Lemma rec_add1_po_1 : 
  (y: Z)
  (Pre8: `y >= 0`)
  (Variant1: Z)
  (y0: Z)
  (x0: Z)
  (Pre7: Variant1 = y0)
  (Pre6: `y0 >= 0`)
  (Test2: `0 < y0`)
  (x1: Z)
  (Post2: x1 = `x0 + 1`)
  `y0 - 1 >= 0`.
Proof.
Intros; Omega.
Save.

Lemma rec_add1_po_2 : 
  (y: Z)
  (Pre8: `y >= 0`)
  (Variant1: Z)
  (y0: Z)
  (x0: Z)
  (Pre7: Variant1 = y0)
  (Pre6: `y0 >= 0`)
  (Test2: `0 < y0`)
  (x1: Z)
  (Post2: x1 = `x0 + 1`)
  (Pre5: `y0 - 1 >= 0`)
  (Pre3: `y0 - 1 >= 0`)
  (Pre4: `y0 - 1 >= 0`)
  (Pre9: `y0 - 1 >= 0`)
  (Zwf `0` `y0 - 1` Variant1).
Proof.
Intros; Unfold Zwf; Omega.
Save.

Lemma rec_add1_po_3 : 
  (y: Z)
  (Pre8: `y >= 0`)
  (Variant1: Z)
  (y0: Z)
  (x0: Z)
  (Pre7: Variant1 = y0)
  (Pre6: `y0 >= 0`)
  (Test2: `0 < y0`)
  (x1: Z)
  (Post2: x1 = `x0 + 1`)
  (Pre5: `y0 - 1 >= 0`)
  (x2: Z)
  (Post7: `x2 = x1 + (y0 - 1)`)
  `x2 = x0 + y0`.
Proof.
Intros; Omega.
Save.

Lemma rec_add1_po_4 : 
  (y: Z)
  (Pre8: `y >= 0`)
  (Variant1: Z)
  (y0: Z)
  (x0: Z)
  (Pre7: Variant1 = y0)
  (Pre6: `y0 >= 0`)
  (Test1: `0 >= y0`)
  `x0 = x0 + y0`.
Proof.
Intros; Omega.
Save.

Definition rec_add1 := (* validation *)
  [y: Z; x: Z; Pre8: `y >= 0`]
    (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`) [Variant1: Z]
      (y0: Z)(x0: Z)(_: Variant1 = y0)(_0: `y0 >= 0`)
      (sig_2 Z unit [x1: Z][result: unit](`x1 = x0 + y0`))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (y0: Z)(x0: Z)(_: Variant2 = y0)(_0: `y0 >= 0`)
       (sig_2 Z unit [x1: Z][result: unit](`x1 = x0 + y0`)); y0: Z; x0: Z;
       Pre7: Variant1 = y0; Pre6: `y0 >= 0`]
        let (result, Bool2) =
          let (result1, Post4) = (Z_lt_ge_bool `0` y0) in
          (exist_1 [result2: bool]
          (if result2 then `0 < y0` else `0 >= y0`) result1 Post4) in
        (Cases (btest [result:bool](if result then `0 < y0` else `0 >= y0`)
                result Bool2) of
        | (left Test2) =>
            let (x1, result0, Post6) =
              let (x1, result0, Post2) =
                let (result0, Post2) = (exist_1 [result0: Z]
                  result0 = `x0 + 1` `x0 + 1` (refl_equal ? `x0 + 1`)) in
                (exist_2 [x2: Z][result1: unit]x2 = `x0 + 1` result0 
                tt Post2) in
              let Pre5 =
                (rec_add1_po_1 y Pre8 Variant1 y0 x0 Pre7 Pre6 Test2 x1
                Post2) in
              let (x2, result1, Post7) =
                let Pre3 = Pre5 in
                let Pre4 = Pre3 in
                let (x2, result3, Post8) =
                  let Pre9 = Pre4 in
                  ((wf1 `y0 - 1`)
                    (rec_add1_po_2 y Pre8 Variant1 y0 x0 Pre7 Pre6 Test2 x1
                    Post2 Pre5 Pre3 Pre4 Pre9) `y0 - 1` x1
                    (refl_equal ? `y0 - 1`) Pre9) in
                (exist_2 [x3: Z][result4: unit]`x3 = x1 + (y0 - 1)` x2
                result3 Post8) in
              (exist_2 [x3: Z][result2: unit]`x3 = x0 + y0` x2 result1
              (rec_add1_po_3 y Pre8 Variant1 y0 x0 Pre7 Pre6 Test2 x1 Post2
              Pre5 x2 Post7)) in
            (exist_2 [x2: Z][result1: unit]`x2 = x0 + y0` x1 result0 Post6)
        | (right Test1) =>
            let (result0, Post5) = (exist_1 [result0: unit]`x0 = x0 + y0` 
              tt (rec_add1_po_4 y Pre8 Variant1 y0 x0 Pre7 Pre6 Test1)) in
            (exist_2 [x1: Z][result1: unit]`x1 = x0 + y0` x0 result0 Post5) end)
      y y x (refl_equal ? y) Pre8).

Lemma u11_po_1 : 
  (result: Z)
  (Post1: result = `3`)
  `7 >= 0`.
Proof.
Intros; Omega.
Save.

Lemma u11_po_2 : 
  (result: Z)
  (Post1: result = `3`)
  (Pre1: `7 >= 0`)
  (r0: Z)
  (Post3: `r0 = result + 7`)
  `r0 = 10`.
Proof.
Intros; Omega.
Save.

Definition u11 := (* validation *)
  let (result, Post1) = (exist_1 [result: Z]result = `3` `3`
    (refl_equal ? `3`)) in
  let (r0, result0, Post2) =
    let Pre1 = (u11_po_1 result Post1) in
    let (r0, result2, Post3) =
      let Pre2 = Pre1 in
      (rec_add1 `7` result Pre2) in
    (exist_2 [r1: Z][result3: unit]`r1 = 10` r0 result2
    (u11_po_2 result Post1 Pre1 r0 Post3)) in
  result0.

Lemma mult1_po_1 : 
  (y: Z)
  (x: Z)
  (Pre6: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post4: result = y)
  (savex: Z)
  (Post3: savex = x)
  (x0: Z)
  (Post1: x0 = `0`)
  (Variant1: Z)
  (x1: Z)
  (z0: Z)
  (Pre5: Variant1 = z0)
  (I: `0 <= z0` /\ `x1 = x * (y - z0)`)
  (Test2: `z0 > 0`)
  `savex >= 0`.
Proof.
Intros; Omega.
Save.

Lemma mult1_po_2 : 
  (y: Z)
  (x: Z)
  (Pre6: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post4: result = y)
  (savex: Z)
  (Post3: savex = x)
  (x0: Z)
  (Post1: x0 = `0`)
  (Variant1: Z)
  (x1: Z)
  (z0: Z)
  (Pre5: Variant1 = z0)
  (I: `0 <= z0` /\ `x1 = x * (y - z0)`)
  (Test2: `z0 > 0`)
  (Pre4: `savex >= 0`)
  (x2: Z)
  (Post8: `x2 = x1 + savex`)
  (z1: Z)
  (Post2: z1 = `z0 - 1`)
  (`0 <= z1` /\ `x2 = x * (y - z1)`) /\ (Zwf `0` z1 z0).
Proof.
Simpl; Intros.
Repeat Split; Unfold Zwf; Try Omega.
Subst z1 x2 savex.
Decompose [and] I.
Subst x1.
Ring.
Save.

Lemma mult1_po_3 : 
  (y: Z)
  (x: Z)
  (Pre6: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post4: result = y)
  (savex: Z)
  (Post3: savex = x)
  (x0: Z)
  (Post1: x0 = `0`)
  `0 <= result` /\ `x0 = x * (y - result)`.
Proof. 
Intros.
Subst result; Split; [ Omega | Ring ]; Assumption.
Save.

Lemma mult1_po_4 : 
  (y: Z)
  (x: Z)
  (Pre6: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post4: result = y)
  (savex: Z)
  (Post3: savex = x)
  (x0: Z)
  (Post1: x0 = `0`)
  (x1: Z)
  (z0: Z)
  (I: (`0 <= z0` /\ `x1 = x * (y - z0)`) /\ `z0 <= 0`)
  `x1 = x * y`.
Proof. 
Simpl; Intros.
Cut `z0 = 0`.
Intros eq; Rewrite eq in I. Intuition.
Generalize H4. Ring `x*(y-0)`. Intro; Ring; Assumption.
Omega.
Save.

Definition mult1 := (* validation *)
  [y: Z; x: Z; Pre6: `x >= 0` /\ `y >= 0`]
    let (result, Post4) = (exist_1 [result: Z]result = y y
      (refl_equal ? y)) in
    let (x0, z0, result0, Post5) =
      let (savex, Post3) = (exist_1 [result0: Z]result0 = x x
        (refl_equal ? x)) in
      let (x0, z0, result0, Post6) =
        let (x0, result0, Post1) =
          let (result0, Post1) = (exist_1 [result0: Z]result0 = `0` `0`
            (refl_equal ? `0`)) in
          (exist_2 [x1: Z][result1: unit]x1 = `0` result0 tt Post1) in
        let (x1, z0, result1, I) =
          (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
            [Variant1: Z](x1: Z)(z0: Z)(_: Variant1 = z0)(I: `0 <= z0` /\
            `x1 = x * (y - z0)`)
            (sig_3 Z Z unit [x2: Z][z1: Z][result1: unit]((`0 <= z1` /\
             `x2 = x * (y - z1)`) /\ `z1 <= 0`))
            [Variant1: Z; wf1: (Variant2: Z)
             (Pre1: (Zwf `0` Variant2 Variant1))(x1: Z)(z0: Z)
             (_: Variant2 = z0)(I: `0 <= z0` /\ `x1 = x * (y - z0)`)
             (sig_3 Z Z unit [x2: Z][z1: Z][result1: unit]((`0 <= z1` /\
              `x2 = x * (y - z1)`) /\ `z1 <= 0`));
             x1: Z; z0: Z; Pre5: Variant1 = z0; I: `0 <= z0` /\
             `x1 = x * (y - z0)`]
              let (result1, Bool1) =
                let (result3, Post7) = (Z_gt_le_bool z0 `0`) in
                (exist_1 [result4: bool]
                (if result4 then `z0 > 0` else `z0 <= 0`) result3 Post7) in
              (Cases (btest
                      [result1:bool](if result1 then `z0 > 0` else `z0 <= 0`)
                      result1 Bool1) of
              | (left Test2) =>
                  let (x2, z1, result2, I0) =
                    let (x2, z1, result2, I0) =
                      let Pre4 =
                        (mult1_po_1 y x Pre6 result Post4 savex Post3 x0
                        Post1 Variant1 x1 z0 Pre5 I Test2) in
                      let (x2, result2, Post8) =
                        let Pre2 = Pre4 in
                        let Pre3 = Pre2 in
                        let (x2, result4, Post9) =
                          let Pre7 = Pre3 in
                          (add1 savex x1 Pre7) in
                        (exist_2 [x3: Z][result5: unit]`x3 = x1 + savex` 
                        x2 result4 Post9) in
                      let (z1, result3, Post2) =
                        let (result3, Post2) = (exist_1 [result3: Z]
                          result3 = `z0 - 1` `z0 - 1`
                          (refl_equal ? `z0 - 1`)) in
                        (exist_2 [z2: Z][result4: unit]z2 = `z0 - 1` 
                        result3 tt Post2) in
                      (exist_3 [x3: Z][z2: Z][result4: unit](`0 <= z2` /\
                      `x3 = x * (y - z2)`) /\ (Zwf `0` z2 z0) x2 z1 result3
                      (mult1_po_2 y x Pre6 result Post4 savex Post3 x0 Post1
                      Variant1 x1 z0 Pre5 I Test2 Pre4 x2 Post8 z1 Post2)) in
                    ((wf1 z1) (loop_variant_1 Pre5 I0) x2 z1
                      (refl_equal ? z1) (proj1 ? ? I0)) in
                  (exist_3 [x3: Z][z2: Z][result3: unit](`0 <= z2` /\
                  `x3 = x * (y - z2)`) /\ `z2 <= 0` x2 z1 result2 I0)
              | (right Test1) =>
                  let (x2, z1, result2, I0) = (exist_3 [x2: Z][z1: Z]
                    [result2: unit](`0 <= z1` /\ `x2 = x * (y - z1)`) /\
                    `z1 <= 0` x1 z0 tt (conj ? ? I Test1)) in
                  (exist_3 [x3: Z][z2: Z][result3: unit](`0 <= z2` /\
                  `x3 = x * (y - z2)`) /\ `z2 <= 0` x2 z1 result2 I0) end)
            result x0 result (refl_equal ? result)
            (mult1_po_3 y x Pre6 result Post4 savex Post3 x0 Post1)) in
        (exist_3 [x2: Z][z1: Z][result2: unit]`x2 = x * y` x1 z0 result1
        (mult1_po_4 y x Pre6 result Post4 savex Post3 x0 Post1 x1 z0 I)) in
      (exist_3 [x1: Z][z1: Z][result1: unit]`x1 = x * y` x0 z0 result0 Post6) in
    (exist_2 [x1: Z][result1: unit]`x1 = x * y` x0 result0 Post5).

Lemma u2_po_1 : 
  (result: Z)
  (Post1: result = `4`)
  `result >= 0` /\ `6 >= 0`.
Proof. Intros; Omega. Save.

Lemma u2_po_2 : 
  (result: Z)
  (Post1: result = `4`)
  (Pre1: `result >= 0` /\ `6 >= 0`)
  (r0: Z)
  (Post3: `r0 = result * 6`)
  `r0 = 24`.
Proof. Intros; Omega. Save.

Definition u2 := (* validation *)
  let (result, Post1) = (exist_1 [result: Z]result = `4` `4`
    (refl_equal ? `4`)) in
  let (r0, result0, Post2) =
    let Pre1 = (u2_po_1 result Post1) in
    let (r0, result2, Post3) = let Pre2 = Pre1 in
                               (mult1 `6` result Pre2) in
    (exist_2 [r1: Z][result3: unit]`r1 = 24` r0 result2
    (u2_po_2 result Post1 Pre1 r0 Post3)) in
  result0.

