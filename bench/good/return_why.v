
Require Why.

(*Why*) Parameter N : Z.

Lemma p_po_1 : 
  (t: (array Z))
  (Pre5: `(array_length t) = N`)
  (i0: Z)
  (Post1: i0 = `0`)
  (Variant1: Z)
  (i1: Z)
  (Pre4: Variant1 = `N - i1`)
  (Pre3: `0 <= i1`)
  (Test4: `i1 < N`)
  `0 <= i1` /\ `i1 < (array_length t)`.
Proof.
Intuition.
Save.

Lemma p_po_2 : 
  (t: (array Z))
  (Pre5: `(array_length t) = N`)
  (i0: Z)
  (Post1: i0 = `0`)
  (Variant1: Z)
  (i1: Z)
  (Pre4: Variant1 = `N - i1`)
  (Pre3: `0 <= i1`)
  (Test4: `i1 < N`)
  (Test3: `(access t i1) = 0`)
  (`0 <= i1` /\ `i1 < N` -> `(access t i1) = 0`).
Proof.
Intuition.
Save.

Lemma p_po_3 : 
  (t: (array Z))
  (Pre5: `(array_length t) = N`)
  (i0: Z)
  (Post1: i0 = `0`)
  (Variant1: Z)
  (i1: Z)
  (Pre4: Variant1 = `N - i1`)
  (Pre3: `0 <= i1`)
  (Test4: `i1 < N`)
  (Test2: `(access t i1) <> 0`)
  ((i:Z) (i = `i1 + 1` -> `0 <= i` /\ (Zwf `0` `N - i` `N - i1`))).
Proof.
Intuition.
Unfold Zwf; Omega.
Save.

Lemma p_po_4 : 
  (t: (array Z))
  (Pre5: `(array_length t) = N`)
  (i0: Z)
  (Post1: i0 = `0`)
  (Variant1: Z)
  (i1: Z)
  (Pre4: Variant1 = `N - i1`)
  (Pre3: `0 <= i1`)
  (Test4: `i1 < N`)
  (Post20: ((i:Z) (i = `i1 + 1` -> `0 <= i` /\ (Zwf `0` `N - i` `N - i1`))))
  (i2: Z)
  (Post2: i2 = `i1 + 1`)
  `0 <= i2` /\ (Zwf `0` `N - i2` `N - i1`).
Proof.
Intuition.
Save.

Lemma p_po_5 : 
  (t: (array Z))
  (Pre5: `(array_length t) = N`)
  (i0: Z)
  (Post1: i0 = `0`)
  `0 <= i0`.
Proof.
Intuition.
Save.


Lemma p_po_6 : 
  (t: (array Z))
  (Pre5: `(array_length t) = N`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (Post3: `0 <= i1` /\ `i1 >= N`)
  (`0 <= N` /\ `N < N` -> `(access t N) = 0`).
Proof.
Intuition.
Save.


Definition p := (* validation *)
  [i: Z; t: (array Z); Pre5: `(array_length t) = N`]
    let (i0, result, Post6) =
      let (i0, result, Post1) =
        let (result, Post1) = (exist_1 [result: Z]result = `0` `0`
          (refl_equal ? `0`)) in
        (exist_2 [i1: Z][result0: unit]i1 = `0` result tt Post1) in
      let (i1, result0, Post7) =
        (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
          [Variant1: Z](i1: Z)(_: Variant1 = `N - i1`)(_0: `0 <= i1`)
          (sig_2 Z (EM Z unit) [i2: Z][result0: (EM Z unit)]
           (((qcomb [result1: Z]
              (`0 <= result1` /\ `result1 < N` -> `(access t result1) = 0`)
              [result1: unit]`0 <= i2` /\ `i2 >= N`)
             result0)))
          [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
           (i1: Z)(_: Variant2 = `N - i1`)(_0: `0 <= i1`)
           (sig_2 Z (EM Z unit) [i2: Z][result0: (EM Z unit)]
            (((qcomb [result1: Z]
               (`0 <= result1` /\ `result1 < N` -> `(access t result1) = 0`)
               [result1: unit]`0 <= i2` /\ `i2 >= N`)
              result0)));
           i1: Z; Pre4: Variant1 = `N - i1`; Pre3: `0 <= i1`]
            let (result0, Bool2) =
              let (result2, Post8) = (Z_lt_ge_bool i1 N) in
              (exist_1 [result3: bool]
              (if result3 then `i1 < N` else `i1 >= N`) result2 Post8) in
            (Cases (btest
                    [result0:bool](if result0 then `i1 < N` else `i1 >= N`)
                    result0 Bool2) of
            | (left Test4) =>
                let (i2, result1, Post11) =
                  let (i2, result1, Post12) =
                    let (result1, Post13) =
                      let (result1, Bool1) =
                        let result2 =
                          let Pre2 =
                            (p_po_1 t Pre5 i0 Post1 Variant1 i1 Pre4 Pre3
                            Test4) in
                          (Z_eq_bool (access t i1)) in
                        let (result3, Post14) = (result2 `0`) in
                        (exist_1 [result4: bool]
                        (if result4 then `(access t i1) = 0`
                         else `(access t i1) <> 0`) result3
                        Post14) in
                      (Cases (btest
                              [result1:bool](if result1
                                             then `(access t i1) = 0`
                                             else `(access t i1) <> 0`)
                              result1 Bool1) of
                      | (left Test3) =>
                          let (result2, Post16) =
                            let (result2, Post17) = (exist_1 [result2: Z]
                              (`0 <= result2` /\ `result2 < N` ->
                               `(access t result2) = 0`) i1
                              (p_po_2 t Pre5 i0 Post1 Variant1 i1 Pre4 Pre3
                              Test4 Test3)) in
                            (exist_1 (qcomb [result3: Z]
                                      (`0 <= result3` /\ `result3 < N` ->
                                       `(access t result3) = 0`)
                                      [result3: unit]
                                      ((i:Z)
                                       (i = `i1 + 1` -> `0 <= i` /\
                                        (Zwf `0` `N - i` `N - i1`)))) 
                            (Exn unit result2) Post17) in
                          Cases (decomp1 Post16) of
                          | (Qval (exist result3 Post18)) =>
                            (exist_1 (qcomb [result4: Z]
                                      (`0 <= result4` /\ `result4 < N` ->
                                       `(access t result4) = 0`)
                                      [result4: unit]
                                      ((i:Z)
                                       (i = `i1 + 1` -> `0 <= i` /\
                                        (Zwf `0` `N - i` `N - i1`)))) 
                            (Val Z result3) Post18)
                          | (Qexn result3 Post19) =>
                            (exist_1 (qcomb [result4: Z]
                                      (`0 <= result4` /\ `result4 < N` ->
                                       `(access t result4) = 0`)
                                      [result4: unit]
                                      ((i:Z)
                                       (i = `i1 + 1` -> `0 <= i` /\
                                        (Zwf `0` `N - i` `N - i1`)))) 
                            (Exn unit result3) Post19)
                          end
                      | (right Test2) =>
                          let (result2, Post15) = (exist_1 [result2: unit]
                            ((i:Z)
                             (i = `i1 + 1` -> `0 <= i` /\
                              (Zwf `0` `N - i` `N - i1`))) tt
                            (p_po_3 t Pre5 i0 Post1 Variant1 i1 Pre4 Pre3
                            Test4 Test2)) in
                          (exist_1 (qcomb [result3: Z]
                                    (`0 <= result3` /\ `result3 < N` ->
                                     `(access t result3) = 0`)
                                    [result3: unit]
                                    ((i:Z)
                                     (i = `i1 + 1` -> `0 <= i` /\
                                      (Zwf `0` `N - i` `N - i1`)))) (Val Z
                                                                    result2)
                          Post15) end) in
                    Cases (decomp1 Post13) of
                    | (Qval (exist result2 Post20)) =>
                      let (i2, result3, Post2) =
                        let (result3, Post2) = (exist_1 [result3: Z]
                          result3 = `i1 + 1` `i1 + 1`
                          (refl_equal ? `i1 + 1`)) in
                        (exist_2 [i3: Z][result4: unit]i3 = `i1 + 1` 
                        result3 tt Post2) in
                      (exist_2 [i3: Z]
                      (qcomb [result4: Z]
                       (`0 <= result4` /\ `result4 < N` ->
                        `(access t result4) = 0`)
                       [result4: unit]`0 <= i3` /\
                       (Zwf `0` `N - i3` `N - i1`)) i2
                      (Val Z result3)
                      (p_po_4 t Pre5 i0 Post1 Variant1 i1 Pre4 Pre3 Test4
                      Post20 i2 Post2))
                    | (Qexn result2 Post21) => (exist_2 [i2: Z]
                      (qcomb [result3: Z]
                       (`0 <= result3` /\ `result3 < N` ->
                        `(access t result3) = 0`)
                       [result3: unit]`0 <= i2` /\
                       (Zwf `0` `N - i2` `N - i1`)) i1 (Exn unit result2)
                      Post21)
                    end in
                  Cases (decomp1 Post12) of
                  | (Qval (exist result2 Post4)) =>
                    ((wf1 `N - i2`) (loop_variant_1 Pre4 Post4) i2
                      (refl_equal ? `N - i2`) (proj1 ? ? Post4))
                  | (Qexn result2 Post22) => (exist_2 [i3: Z]
                    (qcomb [result3: Z]
                     (`0 <= result3` /\ `result3 < N` ->
                      `(access t result3) = 0`)
                     [result3: unit]`0 <= i3` /\ `i3 >= N`) i2
                    (Exn unit result2) Post22)
                  end in
                Cases (decomp1 Post11) of
                | (Qval (exist result2 Post3)) => (exist_2 [i3: Z]
                  (qcomb [result3: Z]
                   (`0 <= result3` /\ `result3 < N` ->
                    `(access t result3) = 0`)
                   [result3: unit]`0 <= i3` /\ `i3 >= N`) i2 (Val Z result2)
                  Post3)
                | (Qexn result2 Post23) => (exist_2 [i3: Z]
                  (qcomb [result3: Z]
                   (`0 <= result3` /\ `result3 < N` ->
                    `(access t result3) = 0`)
                   [result3: unit]`0 <= i3` /\ `i3 >= N`) i2
                  (Exn unit result2) Post23)
                end
            | (right Test1) =>
                let (i2, result1, Post9) = (exist_2 [i2: Z]
                  (qcomb [result1: Z]
                   (`0 <= result1` /\ `result1 < N` ->
                    `(access t result1) = 0`)
                   [result1: unit]`0 <= i2` /\ `i2 >= N`) i1 (Val Z tt)
                  (conj ? ? Pre3 Test1)) in
                Cases (decomp1 Post9) of
                | (Qval (exist result2 Post3)) => (exist_2 [i3: Z]
                  (qcomb [result3: Z]
                   (`0 <= result3` /\ `result3 < N` ->
                    `(access t result3) = 0`)
                   [result3: unit]`0 <= i3` /\ `i3 >= N`) i2 (Val Z result2)
                  Post3)
                | (Qexn result2 Post10) => (exist_2 [i3: Z]
                  (qcomb [result3: Z]
                   (`0 <= result3` /\ `result3 < N` ->
                    `(access t result3) = 0`)
                   [result3: unit]`0 <= i3` /\ `i3 >= N`) i2
                  (Exn unit result2) Post10)
                end end) `N - i0` i0 (refl_equal ? `N - i0`)
          (p_po_5 t Pre5 i0 Post1)) in
      Cases (decomp1 Post7) of
      | (Qval (exist result1 Post3)) =>
        let (result2, Post25) = (exist_1 [result2: Z]
          (`0 <= result2` /\ `result2 < N` -> `(access t result2) = 0`) 
          N (p_po_6 t Pre5 i0 Post1 i1 Post3)) in
        (exist_2 [i2: Z]
        (qcomb [result3: Z]
         (`0 <= result3` /\ `result3 < N` -> `(access t result3) = 0`)
         [result3: Z]
         (`0 <= result3` /\ `result3 < N` -> `(access t result3) = 0`)) 
        i1 (Val Z result2) Post25)
      | (Qexn result1 Post24) => (exist_2 [i2: Z]
        (qcomb [result2: Z]
         (`0 <= result2` /\ `result2 < N` -> `(access t result2) = 0`)
         [result2: Z]
         (`0 <= result2` /\ `result2 < N` -> `(access t result2) = 0`)) 
        i1 (Exn Z result1) Post24)
      end in
    Cases (decomp1 Post6) of
    | (Qval (exist result0 Post26)) => (exist_2 [i1: Z][result1: Z]
      (`0 <= result1` /\ `result1 < N` -> `(access t result1) = 0`) i0
      result0 Post26)
    | (Qexn result0 Post27) =>
      let (result1, Post28) = (exist_1 [result1: Z]
        (`0 <= result1` /\ `result1 < N` -> `(access t result1) = 0`) 
        result0 Post27) in
      (exist_2 [i1: Z][result2: Z]
      (`0 <= result2` /\ `result2 < N` -> `(access t result2) = 0`) i0
      result1 Post28)
    end.

