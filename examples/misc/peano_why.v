
Require Why.
Require Omega.
Require ZArithRing.

Lemma add1_po_1 : 
  (y: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (well_founded ? (Zwf ZERO)).
Proof. Auto with *. Save.

Lemma add1_po_2 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (Variant1: Z)
  (x0: Z)
  (z0: Z)
  (Pre2: Variant1 = z0)
  (I: `0 <= z0` /\ `x0 = x + (y - z0)`)
  (Test2: `z0 > 0`)
  (x1: Z)
  (Post2: x1 = `x0 + 1`)
  (z1: Z)
  (Post3: z1 = `z0 - 1`)
  `0 <= z1` /\ `x1 = x + (y - z1)` /\ (Zwf `0` z1 z0).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma add1_po_3 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (Variant1: Z)
  (x0: Z)
  (z0: Z)
  (Pre2: Variant1 = z0)
  (I: `0 <= z0` /\ `x0 = x + (y - z0)`)
  (Test2: `z0 > 0`)
  (x1: Z)
  (z1: Z)
  (I0: `0 <= z1` /\ `x1 = x + (y - z1)` /\ (Zwf `0` z1 z0))
  (Zwf `0` z1 Variant1).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma add1_po_4 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (Variant1: Z)
  (x0: Z)
  (z0: Z)
  (Pre2: Variant1 = z0)
  (I: `0 <= z0` /\ `x0 = x + (y - z0)`)
  (Test2: `z0 > 0`)
  (x1: Z)
  (z1: Z)
  (I0: `0 <= z1` /\ `x1 = x + (y - z1)` /\ (Zwf `0` z1 z0))
  `0 <= z1` /\ `x1 = x + (y - z1)`.
Proof. Intuition. Save.

Lemma add1_po_5 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (Variant1: Z)
  (x0: Z)
  (z0: Z)
  (Pre2: Variant1 = z0)
  (I: `0 <= z0` /\ `x0 = x + (y - z0)`)
  (Test1: `z0 <= 0`)
  `0 <= z0` /\ `x0 = x + (y - z0)` /\ `z0 <= 0`.
Proof. Intuition. Save.

Lemma add1_po_6 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  `0 <= result` /\ `x = x + (y - result)`.
Proof. Intros; Omega. Save.

Lemma add1_po_7 : 
  (y: Z)
  (x: Z)
  (Pre3: `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (x0: Z)
  (z0: Z)
  (I: `0 <= z0` /\ `x0 = x + (y - z0)` /\ `z0 <= 0`)
  `x0 = x + y`.
Proof. Intros; Omega. Save.

Definition add1 := (* validation *)
  [y: Z; x: Z; Pre3: `y >= 0`]
    let (result, Post1) = (exist_1 [result: Z]result = y y
      (refl_equal ? y)) in
    let (x0, z0, result0, I) =
      (well_founded_induction Z (Zwf ZERO) (add1_po_1 y Pre3 result Post1)
        [Variant1: Z](x0: Z)(z0: Z)(_: Variant1 = z0)(I: `0 <= z0` /\
        `x0 = x + (y - z0)`)
        (sig_3 Z Z unit [x1:Z][z1:Z][result:unit](`0 <= z1` /\
         `x1 = x + (y - z1)` /\ `z1 <= 0`))
        [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
         (x0: Z)(z0: Z)(_: Variant2 = z0)(I: `0 <= z0` /\
         `x0 = x + (y - z0)`)
         (sig_3 Z Z unit [x1:Z][z1:Z][result:unit](`0 <= z1` /\
          `x1 = x + (y - z1)` /\ `z1 <= 0`));
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
              let (x1, z1, result1, I) =
                let (x1, z1, result1, I0) =
                  let (x1, result1, Post2) =
                    let (result1, Post2) = (exist_1 [result1: Z]
                      result1 = `x0 + 1` `x0 + 1` (refl_equal ? `x0 + 1`)) in
                    (exist_2 [x2: Z][result2: unit]x2 = `x0 + 1` result1 
                    tt Post2) in
                  let (z1, result2, Post3) =
                    let (result2, Post3) = (exist_1 [result2: Z]
                      result2 = `z0 - 1` `z0 - 1` (refl_equal ? `z0 - 1`)) in
                    (exist_2 [z2: Z][result3: unit]z2 = `z0 - 1` result2 
                    tt Post3) in
                  (exist_3 [x2: Z][z2: Z][result3: unit]`0 <= z2` /\
                  `x2 = x + (y - z2)` /\ (Zwf `0` z2 z0) x1 z1 result2
                  (add1_po_2 y x Pre3 result Post1 Variant1 x0 z0 Pre2 I
                  Test2 x1 Post2 z1 Post3)) in
                ((wf1 z1)
                  (add1_po_3 y x Pre3 result Post1 Variant1 x0 z0 Pre2 I
                  Test2 x1 z1 I0) x1 z1 (refl_equal ? z1)
                  (add1_po_4 y x Pre3 result Post1 Variant1 x0 z0 Pre2 I
                  Test2 x1 z1 I0)) in
              (exist_3 [x2: Z][z2: Z][result2: unit]`0 <= z2` /\
              `x2 = x + (y - z2)` /\ `z2 <= 0` x1 z1 result1 I)
          | (right Test1) =>
              let (x1, z1, result1, I) = (exist_3 [x1: Z][z1: Z]
                [result1: unit]`0 <= z1` /\ `x1 = x + (y - z1)` /\
                `z1 <= 0` x0 z0 tt
                (add1_po_5 y x Pre3 result Post1 Variant1 x0 z0 Pre2 I Test1)) in
              (exist_3 [x2: Z][z2: Z][result2: unit]`0 <= z2` /\
              `x2 = x + (y - z2)` /\ `z2 <= 0` x1 z1 result1 I) end) 
        result x result (refl_equal ? result)
        (add1_po_6 y x Pre3 result Post1)) in
    (exist_2 [x1: Z][result1: unit]`x1 = x + y` x0 result0
    (add1_po_7 y x Pre3 result Post1 x0 z0 I)).

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
    let (r0, result2, Post3) = (add1 `7` result Pre1) in
    (exist_2 [r1: Z][result3: unit]`r1 = 10` r0 result2
    (u1_po_2 result Post1 Pre1 r0 Post3)) in
  result0.

Lemma rec_add1_po_1 : 
  (y: Z)
  (Pre6: `y >= 0`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma rec_add1_po_2 : 
  (Variant1: Z)
  (y: Z)
  (x0: Z)
  (Pre5: Variant1 = y)
  (Pre4: `y >= 0`)
  (Test2: `0 < y`)
  (x1: Z)
  (Post1: x1 = `x0 + 1`)
  `y - 1 >= 0`.
Proof.
Intros; Omega.
Save.

Lemma rec_add1_po_3 : 
  (Variant1: Z)
  (y: Z)
  (x0: Z)
  (Pre5: Variant1 = y)
  (Pre4: `y >= 0`)
  (Test2: `0 < y`)
  (x1: Z)
  (Post1: x1 = `x0 + 1`)
  (Pre3: `y - 1 >= 0`)
  (Zwf `0` `y - 1` Variant1).
Proof.
Intros; Unfold Zwf; Omega.
Save.

Lemma rec_add1_po_4 : 
  (Variant1: Z)
  (y: Z)
  (x0: Z)
  (Pre5: Variant1 = y)
  (Pre4: `y >= 0`)
  (Test2: `0 < y`)
  (x1: Z)
  (Post1: x1 = `x0 + 1`)
  (x2: Z)
  (Post6: `x2 = x1 + (y - 1)`)
  `x2 = x0 + y`.
Proof.
Intros; Omega.
Save.

Lemma rec_add1_po_5 : 
  (Variant1: Z)
  (y: Z)
  (x0: Z)
  (Pre5: Variant1 = y)
  (Pre4: `y >= 0`)
  (Test1: `0 >= y`)
  `x0 = x0 + y`.
Proof.
Intros; Omega.
Save.

Definition rec_add1 := (* validation *)
  [y: Z; x: Z; Pre6: `y >= 0`]
    (well_founded_induction Z (Zwf ZERO) (rec_add1_po_1 y Pre6) [Variant1: Z]
      (y: Z)(x0: Z)(_: Variant1 = y)(_: `y >= 0`)
      (sig_2 Z unit [x1:Z][result:unit](`x1 = x0 + y`))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (y: Z)(x0: Z)(_: Variant2 = y)(_: `y >= 0`)
       (sig_2 Z unit [x1:Z][result:unit](`x1 = x0 + y`)); y: Z; x0: Z;
       Pre5: Variant1 = y; Pre4: `y >= 0`]
        let (result, Bool1) =
          let (result1, Post3) = (Z_lt_ge_bool `0` y) in
          (exist_1 [result2: bool]
          (if result2 then `0 < y` else `0 >= y`) result1 Post3) in
        (Cases (btest [result:bool](if result then `0 < y` else `0 >= y`)
                result Bool1) of
        | (left Test2) =>
            let (x1, result0, Post5) =
              let (x1, result0, Post1) =
                let (result0, Post1) = (exist_1 [result0: Z]
                  result0 = `x0 + 1` `x0 + 1` (refl_equal ? `x0 + 1`)) in
                (exist_2 [x2: Z][result1: unit]x2 = `x0 + 1` result0 
                tt Post1) in
              let (x2, result1, Post6) =
                let Pre3 =
                  (rec_add1_po_2 Variant1 y x0 Pre5 Pre4 Test2 x1 Post1) in
                let (x2, result3, Post7) =
                  ((wf1 `y - 1`)
                    (rec_add1_po_3 Variant1 y x0 Pre5 Pre4 Test2 x1 Post1
                    Pre3) `y - 1` x1 (refl_equal ? `y - 1`) Pre3) in
                (exist_2 [x3: Z][result4: unit]`x3 = x1 + (y - 1)` x2 
                result3 Post7) in
              (exist_2 [x3: Z][result2: unit]`x3 = x0 + y` x2 result1
              (rec_add1_po_4 Variant1 y x0 Pre5 Pre4 Test2 x1 Post1 x2 Post6)) in
            (exist_2 [x2: Z][result1: unit]`x2 = x0 + y` x1 result0 Post5)
        | (right Test1) =>
            let (result0, Post4) = (exist_1 [result0: unit]`x0 = x0 + y` 
              tt (rec_add1_po_5 Variant1 y x0 Pre5 Pre4 Test1)) in
            (exist_2 [x1: Z][result1: unit]`x1 = x0 + y` x0 result0 Post4) end)
      y y x (refl_equal ? y) Pre6).

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
    let (r0, result2, Post3) = (rec_add1 `7` result Pre1) in
    (exist_2 [r1: Z][result3: unit]`r1 = 10` r0 result2
    (u11_po_2 result Post1 Pre1 r0 Post3)) in
  result0.

Lemma mult1_po_1 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (savex: Z)
  (Post2: savex = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (well_founded ? (Zwf ZERO)).
Proof. Auto with *. Save.

Lemma mult1_po_2 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (savex: Z)
  (Post2: savex = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (Variant1: Z)
  (x1: Z)
  (z0: Z)
  (Pre3: Variant1 = z0)
  (I: `0 <= z0` /\ `x1 = x * (y - z0)`)
  (Test2: `z0 > 0`)
  `savex >= 0`.
Proof.
Intros; Omega.
Save.

Lemma mult1_po_3 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (savex: Z)
  (Post2: savex = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (Variant1: Z)
  (x1: Z)
  (z0: Z)
  (Pre3: Variant1 = z0)
  (I: `0 <= z0` /\ `x1 = x * (y - z0)`)
  (Test2: `z0 > 0`)
  (x2: Z)
  (Post8: `x2 = x1 + savex`)
  (z1: Z)
  (Post4: z1 = `z0 - 1`)
  `0 <= z1` /\ `x2 = x * (y - z1)` /\ (Zwf `0` z1 z0).
Proof. 
Simpl; Intros.
Repeat Split; Unfold Zwf; Try Omega.
Rewrite Post4; Clear Post4.
Rewrite Post8; Clear Post8.
Rewrite Post2; Clear Post2.
Decompose [and] I.
Rewrite H0; Clear H0.
Ring.
Save.

Lemma mult1_po_4 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (savex: Z)
  (Post2: savex = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (Variant1: Z)
  (x1: Z)
  (z0: Z)
  (Pre3: Variant1 = z0)
  (I: `0 <= z0` /\ `x1 = x * (y - z0)`)
  (Test2: `z0 > 0`)
  (x2: Z)
  (z1: Z)
  (I0: `0 <= z1` /\ `x2 = x * (y - z1)` /\ (Zwf `0` z1 z0))
  (Zwf `0` z1 Variant1).
Proof. 
Simpl; Intros.
Rewrite Pre3; Tauto.
Save.

Lemma mult1_po_5 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (savex: Z)
  (Post2: savex = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (Variant1: Z)
  (x1: Z)
  (z0: Z)
  (Pre3: Variant1 = z0)
  (I: `0 <= z0` /\ `x1 = x * (y - z0)`)
  (Test2: `z0 > 0`)
  (x2: Z)
  (z1: Z)
  (I0: `0 <= z1` /\ `x2 = x * (y - z1)` /\ (Zwf `0` z1 z0))
  `0 <= z1` /\ `x2 = x * (y - z1)`.
Proof.
Tauto.
Save.

Lemma mult1_po_6 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (savex: Z)
  (Post2: savex = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (Variant1: Z)
  (x1: Z)
  (z0: Z)
  (Pre3: Variant1 = z0)
  (I: `0 <= z0` /\ `x1 = x * (y - z0)`)
  (Test1: `z0 <= 0`)
  `0 <= z0` /\ `x1 = x * (y - z0)` /\ `z0 <= 0`.
Proof. Tauto. Save.

Lemma mult1_po_7 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (savex: Z)
  (Post2: savex = x)
  (x0: Z)
  (Post3: x0 = `0`)
  `0 <= result` /\ `x0 = x * (y - result)`.
Proof. Intros.
Rewrite Post1; Split; [ Omega | Ring ]; Assumption.
Save.

Lemma mult1_po_8 : 
  (y: Z)
  (x: Z)
  (Pre4: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = y)
  (savex: Z)
  (Post2: savex = x)
  (x0: Z)
  (Post3: x0 = `0`)
  (x1: Z)
  (z0: Z)
  (I: `0 <= z0` /\ `x1 = x * (y - z0)` /\ `z0 <= 0`)
  `x1 = x * y`.
Proof.
Simpl; Intros.
Cut `z0 = 0`.
Intros eq; Rewrite eq in I. Decompose [and] I.
Generalize H1. Ring `x*(y-0)`. Intro; Ring; Assumption.
Omega.
Save.

Definition mult1 := (* validation *)
  [y: Z; x: Z; Pre4: `x >= 0` /\ `y >= 0`]
    let (result, Post1) = (exist_1 [result: Z]result = y y
      (refl_equal ? y)) in
    let (x0, z0, result0, Post5) =
      let (savex, Post2) = (exist_1 [result0: Z]result0 = x x
        (refl_equal ? x)) in
      let (x0, z0, result0, Post6) =
        let (x0, result0, Post3) =
          let (result0, Post3) = (exist_1 [result0: Z]result0 = `0` `0`
            (refl_equal ? `0`)) in
          (exist_2 [x1: Z][result1: unit]x1 = `0` result0 tt Post3) in
        let (x1, z0, result1, I) =
          (well_founded_induction Z (Zwf ZERO)
            (mult1_po_1 y x Pre4 result Post1 savex Post2 x0 Post3)
            [Variant1: Z](x1: Z)(z0: Z)(_: Variant1 = z0)(I: `0 <= z0` /\
            `x1 = x * (y - z0)`)
            (sig_3 Z Z unit [x2:Z][z1:Z][result:unit](`0 <= z1` /\
             `x2 = x * (y - z1)` /\ `z1 <= 0`))
            [Variant1: Z; wf1: (Variant2: Z)
             (Pre1: (Zwf `0` Variant2 Variant1))(x1: Z)(z0: Z)
             (_: Variant2 = z0)(I: `0 <= z0` /\ `x1 = x * (y - z0)`)
             (sig_3 Z Z unit [x2:Z][z1:Z][result:unit](`0 <= z1` /\
              `x2 = x * (y - z1)` /\ `z1 <= 0`));
             x1: Z; z0: Z; Pre3: Variant1 = z0; I: `0 <= z0` /\
             `x1 = x * (y - z0)`]
              let (result1, Bool1) =
                let (result3, Post7) = (Z_gt_le_bool z0 `0`) in
                (exist_1 [result4: bool]
                (if result4 then `z0 > 0` else `z0 <= 0`) result3 Post7) in
              (Cases (btest
                      [result1:bool](if result1 then `z0 > 0` else `z0 <= 0`)
                      result1 Bool1) of
              | (left Test2) =>
                  let (x2, z1, result2, I) =
                    let (x2, z1, result2, I0) =
                      let (x2, result2, Post8) =
                        let Pre2 =
                          (mult1_po_2 y x Pre4 result Post1 savex Post2 x0
                          Post3 Variant1 x1 z0 Pre3 I Test2) in
                        let (x2, result4, Post9) = (add1 savex x1 Pre2) in
                        (exist_2 [x3: Z][result5: unit]`x3 = x1 + savex` 
                        x2 result4 Post9) in
                      let (z1, result3, Post4) =
                        let (result3, Post4) = (exist_1 [result3: Z]
                          result3 = `z0 - 1` `z0 - 1`
                          (refl_equal ? `z0 - 1`)) in
                        (exist_2 [z2: Z][result4: unit]z2 = `z0 - 1` 
                        result3 tt Post4) in
                      (exist_3 [x3: Z][z2: Z][result4: unit]`0 <= z2` /\
                      `x3 = x * (y - z2)` /\ (Zwf `0` z2 z0) x2 z1 result3
                      (mult1_po_3 y x Pre4 result Post1 savex Post2 x0 Post3
                      Variant1 x1 z0 Pre3 I Test2 x2 Post8 z1 Post4)) in
                    ((wf1 z1)
                      (mult1_po_4 y x Pre4 result Post1 savex Post2 x0 Post3
                      Variant1 x1 z0 Pre3 I Test2 x2 z1 I0) x2 z1
                      (refl_equal ? z1)
                      (mult1_po_5 y x Pre4 result Post1 savex Post2 x0 Post3
                      Variant1 x1 z0 Pre3 I Test2 x2 z1 I0)) in
                  (exist_3 [x3: Z][z2: Z][result3: unit]`0 <= z2` /\
                  `x3 = x * (y - z2)` /\ `z2 <= 0` x2 z1 result2 I)
              | (right Test1) =>
                  let (x2, z1, result2, I) = (exist_3 [x2: Z][z1: Z]
                    [result2: unit]`0 <= z1` /\ `x2 = x * (y - z1)` /\
                    `z1 <= 0` x1 z0 tt
                    (mult1_po_6 y x Pre4 result Post1 savex Post2 x0 Post3
                    Variant1 x1 z0 Pre3 I Test1)) in
                  (exist_3 [x3: Z][z2: Z][result3: unit]`0 <= z2` /\
                  `x3 = x * (y - z2)` /\ `z2 <= 0` x2 z1 result2 I) end)
            result x0 result (refl_equal ? result)
            (mult1_po_7 y x Pre4 result Post1 savex Post2 x0 Post3)) in
        (exist_3 [x2: Z][z1: Z][result2: unit]`x2 = x * y` x1 z0 result1
        (mult1_po_8 y x Pre4 result Post1 savex Post2 x0 Post3 x1 z0 I)) in
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
    let (r0, result2, Post3) = (mult1 `6` result Pre1) in
    (exist_2 [r1: Z][result3: unit]`r1 = 24` r0 result2
    (u2_po_2 result Post1 Pre1 r0 Post3)) in
  result0.

