
Require Why.
Require Omega.

Lemma loop1_po_1 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with datatypes.
Save.

Lemma loop1_po_2 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: Variant1 = `10 - i0`)
  (Pre4: `i0 <= 10`)
  (Test2: `i0 < 10`)
  (Pre3: `i0 <= 10`)
  (i1: Z)
  (Post1: i1 = `i0 + 1`)
  `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma loop1_po_3 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: Variant1 = `10 - i0`)
  (Pre4: `i0 <= 10`)
  (Test2: `i0 < 10`)
  (Pre3: `i0 <= 10`)
  (i1: Z)
  (Post2: `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`))
  (Zwf `0` `10 - i1` Variant1).
Proof.
Intros. Rewrite Pre5; Tauto.
Save.

Lemma loop1_po_4 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: Variant1 = `10 - i0`)
  (Pre4: `i0 <= 10`)
  (Test2: `i0 < 10`)
  (Pre3: `i0 <= 10`)
  (i1: Z)
  (Post2: `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`))
  `i1 <= 10`.
Proof.
Intros. Simpl in Test2; Omega.
Save.

Lemma loop1_po_5 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: Variant1 = `10 - i0`)
  (Pre4: `i0 <= 10`)
  (Test1: `i0 >= 10`)
  (Pre2: `i0 <= 10`)
  `i0 = 10`.
Proof.
Simpl; Intros; Omega.
Save.

Definition loop1 := (* validation *)
  [i: Z; Pre6: `i <= 10`]
    (well_founded_induction Z (Zwf ZERO) (loop1_po_1 i Pre6) [Variant1: Z]
      (i0: Z)(_: Variant1 = `10 - i0`)(_0: `i0 <= 10`)
      (sig_2 Z unit [i1: Z][result: unit](`i1 = 10`))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (i0: Z)(_: Variant2 = `10 - i0`)(_0: `i0 <= 10`)
       (sig_2 Z unit [i1: Z][result: unit](`i1 = 10`)); i0: Z;
       Pre5: Variant1 = `10 - i0`; Pre4: `i0 <= 10`]
        let (result, Bool1) =
          let (result1, Post3) = (Z_lt_ge_bool i0 `10`) in
          (exist_1 [result2: bool]
          (if result2 then `i0 < 10` else `i0 >= 10`) result1 Post3) in
        (Cases (btest [result:bool](if result then `i0 < 10` else `i0 >= 10`)
                result Bool1) of
        | (left Test2) =>
            let Pre3 = Pre4 in
            let (i1, result0, Post5) =
              let (i1, result0, Post2) =
                let (i1, result0, Post1) =
                  let (result0, Post1) = (exist_1 [result0: Z]
                    result0 = `i0 + 1` `i0 + 1` (refl_equal ? `i0 + 1`)) in
                  (exist_2 [i2: Z][result1: unit]i2 = `i0 + 1` result0 
                  tt Post1) in
                (exist_2 [i2: Z][result1: unit]`i2 <= 10` /\
                (Zwf `0` `10 - i2` `10 - i0`) i1 result0
                (loop1_po_2 i Pre6 Variant1 i0 Pre5 Pre4 Test2 Pre3 i1 Post1)) in
              ((wf1 `10 - i1`)
                (loop1_po_3 i Pre6 Variant1 i0 Pre5 Pre4 Test2 Pre3 i1 Post2)
                i1 (refl_equal ? `10 - i1`)
                (loop1_po_4 i Pre6 Variant1 i0 Pre5 Pre4 Test2 Pre3 i1 Post2)) in
            (exist_2 [i2: Z][result1: unit]`i2 = 10` i1 result0 Post5)
        | (right Test1) =>
            let Pre2 = Pre4 in
            let (i1, result0, Post4) = (exist_2 [i1: Z][result0: unit]
              `i1 = 10` i0 tt
              (loop1_po_5 i Pre6 Variant1 i0 Pre5 Pre4 Test1 Pre2)) in
            (exist_2 [i2: Z][result1: unit]`i2 = 10` i1 result0 Post4) end)
      `10 - i` i (refl_equal ? `10 - i`) Pre6).

Definition oppose := (* validation *)
  [u: unit; x: Z]
    let (result, Post1) = (exist_1 [result: Z]`result = (-x)` `(-x)`
      (refl_equal ? `(-x)`)) in
    (exist_2 [x1: Z][result0: unit]`x1 = (-x)` result tt Post1).

Lemma loop2_po_1 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with datatypes.
Save.

Lemma loop2_po_2 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = `10 - x0`)
  (Pre2: `x0 <= 10`)
  (Test2: `x0 < 10`)
  (x1: Z)
  (Post1: x1 = `x0 + 1`)
  `x1 <= 10` /\ (Zwf `0` `10 - x1` `10 - x0`).
Proof.
Unfold Zwf; Intros; Omega.
Save.

Lemma loop2_po_3 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = `10 - x0`)
  (Pre2: `x0 <= 10`)
  (Test2: `x0 < 10`)
  (x1: Z)
  (Post3: `x1 <= 10` /\ (Zwf `0` `10 - x1` `10 - x0`))
  (Zwf `0` `10 - x1` Variant1).
Proof.
Intros; Rewrite Pre3; Tauto.
Save.

Lemma loop2_po_4 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = `10 - x0`)
  (Pre2: `x0 <= 10`)
  (Test2: `x0 < 10`)
  (x1: Z)
  (Post3: `x1 <= 10` /\ (Zwf `0` `10 - x1` `10 - x0`))
  `x1 <= 10`.
Proof.
Intros; Intuition.
Save.

Lemma loop2_po_5 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (Variant1: Z)
  (x0: Z)
  (Pre3: Variant1 = `10 - x0`)
  (Pre2: `x0 <= 10`)
  (Test1: `x0 >= 10`)
  `x0 = 10`.
Proof.
Simpl; Intros; Omega.
Save.

Lemma loop2_po_6 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (x0: Z)
  (Post4: `x0 = 10`)
  (Test4: `x0 > 0`)
  (x1: Z)
  (Post11: `x1 = (-x0)`)
  `x1 = (-10)`.
Proof.
Intros; Omega.
Save.

Lemma loop2_po_7 : 
  (x: Z)
  (Pre4: `x <= 10`)
  (x0: Z)
  (Post4: `x0 = 10`)
  (Test3: `x0 <= 0`)
  `x0 = (-10)`.
Proof.
Intros; Omega.
Save.



Definition loop2 := (* validation *)
  [x: Z; Pre4: `x <= 10`]
    let (x0, result, Post4) =
      (well_founded_induction Z (Zwf ZERO) (loop2_po_1 x Pre4) [Variant1: Z]
        (x0: Z)(_: Variant1 = `10 - x0`)(_0: `x0 <= 10`)
        (sig_2 Z unit [x1: Z][result: unit](`x1 = 10`))
        [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
         (x0: Z)(_: Variant2 = `10 - x0`)(_0: `x0 <= 10`)
         (sig_2 Z unit [x1: Z][result: unit](`x1 = 10`)); x0: Z;
         Pre3: Variant1 = `10 - x0`; Pre2: `x0 <= 10`]
          let (result, Bool1) =
            let (result1, Post5) = (Z_lt_ge_bool x0 `10`) in
            (exist_1 [result2: bool]
            (if result2 then `x0 < 10` else `x0 >= 10`) result1 Post5) in
          (Cases (btest
                  [result:bool](if result then `x0 < 10` else `x0 >= 10`)
                  result Bool1) of
          | (left Test2) =>
              let (x1, result0, Post7) =
                let (x1, result0, Post3) =
                  let (x1, result0, Post1) =
                    let (result0, Post1) = (exist_1 [result0: Z]
                      result0 = `x0 + 1` `x0 + 1` (refl_equal ? `x0 + 1`)) in
                    (exist_2 [x2: Z][result1: unit]x2 = `x0 + 1` result0 
                    tt Post1) in
                  (exist_2 [x2: Z][result1: unit]`x2 <= 10` /\
                  (Zwf `0` `10 - x2` `10 - x0`) x1 result0
                  (loop2_po_2 x Pre4 Variant1 x0 Pre3 Pre2 Test2 x1 Post1)) in
                ((wf1 `10 - x1`)
                  (loop2_po_3 x Pre4 Variant1 x0 Pre3 Pre2 Test2 x1 Post3) 
                  x1 (refl_equal ? `10 - x1`)
                  (loop2_po_4 x Pre4 Variant1 x0 Pre3 Pre2 Test2 x1 Post3)) in
              (exist_2 [x2: Z][result1: unit]`x2 = 10` x1 result0 Post7)
          | (right Test1) =>
              let (x1, result0, Post6) = (exist_2 [x1: Z][result0: unit]
                `x1 = 10` x0 tt
                (loop2_po_5 x Pre4 Variant1 x0 Pre3 Pre2 Test1)) in
              (exist_2 [x2: Z][result1: unit]`x2 = 10` x1 result0 Post6) end)
        `10 - x` x (refl_equal ? `10 - x`) Pre4) in
    let (x1, result0, Post8) =
      let (result0, Bool2) =
        let (result2, Post9) = (Z_gt_le_bool x0 `0`) in
        (exist_1 [result3: bool]
        (if result3 then `x0 > 0` else `x0 <= 0`) result2 Post9) in
      (Cases (btest [result0:bool](if result0 then `x0 > 0` else `x0 <= 0`)
              result0 Bool2) of
      | (left Test4) =>
          let (x1, result1, Post11) =
            let (x1, result3, Post12) = (oppose tt x0) in
            (exist_2 [x2: Z][result4: unit]`x2 = (-x0)` x1 result3 Post12) in
          (exist_2 [x2: Z][result2: unit]`x2 = (-10)` x1 result1
          (loop2_po_6 x Pre4 x0 Post4 Test4 x1 Post11))
      | (right Test3) =>
          let (result1, Post10) = (exist_1 [result1: unit]`x0 = (-10)` 
            tt (loop2_po_7 x Pre4 x0 Post4 Test3)) in
          (exist_2 [x1: Z][result2: unit]`x1 = (-10)` x0 result1 Post10) end) in
    (Build_tuple_2 x1 result0).

