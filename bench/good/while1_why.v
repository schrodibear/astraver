
Require Why.
Require Omega.

Lemma p_po_1 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with datatypes.
Save.

Lemma p_po_2 : 
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

Lemma p_po_3 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: Variant1 = `10 - i0`)
  (Pre4: `i0 <= 10`)
  (Test2: `i0 < 10`)
  (Pre3: `i0 <= 10`)
  (i1: Z)
  (Post5: `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`))
  (Zwf `0` `10 - i1` Variant1).
Proof. 
Intros. Rewrite Pre5; Tauto.
Save.

Lemma p_po_4 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: Variant1 = `10 - i0`)
  (Pre4: `i0 <= 10`)
  (Test2: `i0 < 10`)
  (Pre3: `i0 <= 10`)
  (i1: Z)
  (Post5: `i1 <= 10` /\ (Zwf `0` `10 - i1` `10 - i0`))
  `i1 <= 10`.
Proof.
Intros. Simpl in Test2; Omega.
Save.

Lemma p_po_5 : 
  (i: Z)
  (Pre6: `i <= 10`)
  (Variant1: Z)
  (i0: Z)
  (Pre5: Variant1 = `10 - i0`)
  (Pre4: `i0 <= 10`)
  (Test1: `i0 >= 10`)
  (Pre2: `i0 <= 10`)
  i0 = `10`.
Proof.
Simpl; Intros; Omega.
Save.















Definition p := (* validation *)
  [i: Z]
    [Pre6: `i <= 10`]
      (((((((((well_founded_induction Z) (Zwf ZERO)) (p_po_1 i Pre6))
             [Variant1: Z](i0: Z)(_: Variant1 = `10 - i0`)(_: `i0 <= 10`)(sig_2 Z
             unit [i1:Z][result:unit](i1 = `10`)))
            [Variant1: Z]
              [wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))(i0: Z)(_: 
                Variant2 = `10 - i0`)(_: `i0 <= 10`)(sig_2 Z
                unit [i1:Z][result:unit](i1 = `10`))]
                [i0: Z]
                  [Pre5: Variant1 = `10 - i0`]
                    [Pre4: `i0 <= 10`]
                      let (result, Bool1) =
                        let (result1, Post2) = (Z_lt_ge_bool i0 `10`) in
                        (exist_1 [result2: bool](if result2 then `i0 < 10`
                                                 else `i0 >= 10`) result1
                        Post2) in
                      (Cases (btest [result:bool](if result then `i0 < 10`
                                                  else `i0 >= 10`) result Bool1) of
                      | (left Test2) =>
                          let Pre3 = Pre4 in
                          let (i1, result0, Post4) =
                            let (i1, result0, Post5) =
                              let (i1, result0, Post1) =
                                let (result0, Post1) =
                                  (exist_1 [result0: Z]result0 = `i0 + 1` 
                                  `i0 + 1` (refl_equal ? `i0 + 1`)) in
                                (exist_2 [i2: Z][result1: unit]i2 = `i0 + 1` 
                                result0 tt Post1) in
                              (exist_2 [i2: Z][result1: unit]`i2 <= 10` /\
                              (Zwf `0` `10 - i2` `10 - i0`) i1 result0
                              (p_po_2 i Pre6 Variant1 i0 Pre5 Pre4 Test2 Pre3
                              i1 Post1)) in
                            (((((wf1 `10 - i1`)
                                 (p_po_3 i Pre6 Variant1 i0 Pre5 Pre4 Test2
                                 Pre3 i1 Post5)) i1)
                               (refl_equal ? `10 - i1`))
                              (p_po_4 i Pre6 Variant1 i0 Pre5 Pre4 Test2 Pre3
                              i1 Post5)) in
                          (exist_2 [i2: Z][result1: unit]i2 = `10` i1 
                          result0 Post4)
                      | (right Test1) =>
                          let Pre2 = Pre4 in
                          let (i1, result0, Post3) =
                            (exist_2 [i1: Z][result0: unit]i1 = `10` 
                            i0 tt
                            (p_po_5 i Pre6 Variant1 i0 Pre5 Pre4 Test1 Pre2)) in
                          (exist_2 [i2: Z][result1: unit]i2 = `10` i1 
                          result0 Post3) end)) `10 - i`) i)
         (refl_equal ? `10 - i`)) Pre6).

