(* This file is generated by Why; do not edit *)

Require Why.
Require Export maximumsort_why.

Definition swap (* validation *)
  : (i: Z)(j: Z)(t: (array Z))(_: (`0 <= i` /\ `i < (array_length t)`) /\
    `0 <= j` /\ `j < (array_length t)`)
    (sig_2 (array Z) unit [t0: (array Z)][result: unit]((exchange t0 t i j)))
  := [i: Z; j: Z; t: (array Z); Pre5: (`0 <= i` /\ `i < (array_length t)`) /\
      `0 <= j` /\ `j < (array_length t)`]
       let Pre4 = (proj1 ? ? Pre5) in
       let (v, Post3) = (exist_1 [result: Z]
         result = (access t i) (access t i) (refl_equal ? (access t i))) in
       let (t0, result, Post4) =
         let Pre2 = Pre4 in
         let Pre3 = (swap_po_1 i j t Pre5 Pre4 v Post3 Pre2) in
         let (t0, result, Post1) = (exist_2 [t1: (array Z)][result1: unit]
           t1 = (store t i (access t j)) (store t i (access t j)) tt
           (refl_equal ? (store t i (access t j)))) in
         let Pre1 = (swap_po_2 i j t Pre5 Pre4 v Post3 Pre2 Pre3 t0 Post1) in
         let (t1, result0, Post2) = (exist_2 [t2: (array Z)][result2: unit]
           t2 = (store t0 j v) (store t0 j v) tt
           (refl_equal ? (store t0 j v))) in
         (exist_2 [t2: (array Z)][result1: unit](exchange t2 t i j) t1
         result0
         (swap_po_3 i j t Pre5 Pre4 v Post3 Pre2 Pre3 t0 Post1 Pre1 t1 Post2)) in
       (exist_2 [t1: (array Z)][result0: unit](exchange t1 t i j) t0 
       result Post4).

Definition maximum (* validation *)
  : (n: Z)(k: Z)(i: Z)(t: (array Z))(_: (`0 <= k` /\ `k <= i`) /\ `i <= n` /\
    `n < (array_length t)` /\ (Maximize t n (access t i) k))
    (sig_1 Z [result: Z]((`0 <= result` /\ `result <= n`) /\
     (Maximize t n (access t result) `0`)))
  := [n: Z; k: Z; i: Z; t: (array Z); Pre14: (`0 <= k` /\ `k <= i`) /\
      `i <= n` /\ `n < (array_length t)` /\ (Maximize t n (access t i) k)]
       (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
         [Variant1: Z](n0: Z)(k0: Z)(i0: Z)(_: Variant1 = k0)
         (_0: (`0 <= k0` /\ `k0 <= i0`) /\ `i0 <= n0` /\
         `n0 < (array_length t)` /\ (Maximize t n0 (access t i0) k0))
         (sig_1 Z [result: Z]((`0 <= result` /\ `result <= n0`) /\
          (Maximize t n0 (access t result) `0`)))
         [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
          (n0: Z)(k0: Z)(i0: Z)(_: Variant2 = k0)(_0: (`0 <= k0` /\
          `k0 <= i0`) /\ `i0 <= n0` /\ `n0 < (array_length t)` /\
          (Maximize t n0 (access t i0) k0))
          (sig_1 Z [result: Z]((`0 <= result` /\ `result <= n0`) /\
           (Maximize t n0 (access t result) `0`)));
          n0: Z; k0: Z; i0: Z; Pre13: Variant1 = k0; Pre12: (`0 <= k0` /\
          `k0 <= i0`) /\ `i0 <= n0` /\ `n0 < (array_length t)` /\
          (Maximize t n0 (access t i0) k0)]
           let (result, Bool6) =
             let (result1, Post6) = (Z_eq_bool k0 `0`) in
             (exist_1 [result2: bool]
             (if result2 then `k0 = 0` else `k0 <> 0`) result1 Post6) in
           Cases
             (btest
              [result:bool](if result then `k0 = 0` else `k0 <> 0`) result
              Bool6) of
           | (left Test4) =>
               let (result0, Post14) = (exist_1 [result0: Z]
                 (`0 <= result0` /\ `result0 <= n0`) /\
                 (Maximize t n0 (access t result0) `0`) i0
                 (maximum_po_1 n k i t Pre14 Variant1 n0 k0 i0 Pre13 Pre12
                 Test4)) in
               (exist_1 [result1: Z](`0 <= result1` /\ `result1 <= n0`) /\
               (Maximize t n0 (access t result1) `0`) result0 Post14)
           | (right Test3) =>
               let (result0, Post7) =
                 let (nk, Post3) = (exist_1 [result0: Z]
                   result0 = `k0 - 1` `k0 - 1` (refl_equal ? `k0 - 1`)) in
                 let (result0, Post8) =
                   let (result0, Bool5) =
                     let Pre3 =
                       (maximum_po_2 n k i t Pre14 Variant1 n0 k0 i0 Pre13
                       Pre12 Test3 nk Post3) in
                     let result1 =
                       let Pre2 =
                         (maximum_po_3 n k i t Pre14 Variant1 n0 k0 i0 Pre13
                         Pre12 Test3 nk Post3 Pre3) in
                       (Z_gt_le_bool (access t nk)) in
                     let (result2, Post9) = (result1 (access t i0)) in
                     (exist_1 [result3: bool]
                     (if result3 then `(access t nk) > (access t i0)`
                      else `(access t nk) <= (access t i0)`) result2
                     Post9) in
                   Cases
                     (btest
                      [result0:bool]
                      (if result0 then `(access t nk) > (access t i0)`
                       else `(access t nk) <= (access t i0)`) result0
                      Bool5) of
                   | (left Test2) =>
                       let Pre11 =
                         (maximum_po_4 n k i t Pre14 Variant1 n0 k0 i0 Pre13
                         Pre12 Test3 nk Post3 Test2) in
                       let (result1, Post12) =
                         let Pre9 = Pre11 in
                         let Pre10 = Pre9 in
                         let (result3, Post13) =
                           ((wf1 nk)
                             (maximum_po_5 n k i t Pre14 Variant1 n0 k0 i0
                             Pre13 Pre12 Test3 nk Post3 Test2 Pre11 Pre9
                             Pre10) n0 nk nk (refl_equal ? nk) Pre10) in
                         (exist_1 [result4: Z](`0 <= result4` /\
                         `result4 <= n0`) /\
                         (Maximize t n0 (access t result4) `0`) result3
                         Post13) in
                       (exist_1 [result2: Z](`0 <= result2` /\
                       `result2 <= n0`) /\
                       (Maximize t n0 (access t result2) `0`) result1 Post12)
                   | (right Test1) =>
                       let Pre7 =
                         (maximum_po_6 n k i t Pre14 Variant1 n0 k0 i0 Pre13
                         Pre12 Test3 nk Post3 Test1) in
                       let (result1, Post10) =
                         let Pre5 = Pre7 in
                         let Pre6 = Pre5 in
                         let (result3, Post11) =
                           ((wf1 nk)
                             (maximum_po_7 n k i t Pre14 Variant1 n0 k0 i0
                             Pre13 Pre12 Test3 nk Post3 Test1 Pre7 Pre5 Pre6)
                             n0 nk i0 (refl_equal ? nk) Pre6) in
                         (exist_1 [result4: Z](`0 <= result4` /\
                         `result4 <= n0`) /\
                         (Maximize t n0 (access t result4) `0`) result3
                         Post11) in
                       (exist_1 [result2: Z](`0 <= result2` /\
                       `result2 <= n0`) /\
                       (Maximize t n0 (access t result2) `0`) result1 Post10) end in
                 (exist_1 [result1: Z](`0 <= result1` /\ `result1 <= n0`) /\
                 (Maximize t n0 (access t result1) `0`) result0 Post8) in
               (exist_1 [result1: Z](`0 <= result1` /\ `result1 <= n0`) /\
               (Maximize t n0 (access t result1) `0`) result0 Post7) end 
         k n k i (refl_equal ? k) Pre14).

Definition maxisort (* validation *)
  : (t: (array Z))(_: `0 <= (array_length t)`)
    (sig_2 (array Z) unit [t0: (array Z)][result: unit]
     ((sorted_array t0 `0` `(array_length t0) - 1`) /\ (permut t0 t)))
  := [t: (array Z); Pre10: `0 <= (array_length t)`]
       let (t0, result, Post5) =
         let (result, Post3) = (exist_1 [result: Z]
           result = `(array_length t) - 1` `(array_length t) - 1`
           (refl_equal ? `(array_length t) - 1`)) in
         let (i0, t0, result0, Post2) =
           (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
             [Variant1: Z](i0: Z)(t0: (array Z))(_: Variant1 = `i0 + 1`)
             (_0: (`0 <= i0 + 1` /\ `i0 + 1 <= (array_length t0)`) /\
             (sorted_array t0 `i0 + 1` `(array_length t0) - 1`) /\
             (permut t0 t) /\
             ((`i0 + 1 < (array_length t0)` ->
               (Maximize t0 i0 (access t0 `i0 + 1`) `0`))))
             (sig_3 Z (array Z) unit [i1: Z][t1: (array Z)][result0: unit]
              (((`0 <= i1 + 1` /\ `i1 + 1 <= (array_length t1)`) /\
              (sorted_array t1 `i1 + 1` `(array_length t1) - 1`) /\
              (permut t1 t) /\
              ((`i1 + 1 < (array_length t1)` ->
                (Maximize t1 i1 (access t1 `i1 + 1`) `0`)))) /\
              `i1 < 0`))
             [Variant1: Z; wf1: (Variant2: Z)
              (Pre1: (Zwf `0` Variant2 Variant1))(i0: Z)(t0: (array Z))
              (_: Variant2 = `i0 + 1`)(_0: (`0 <= i0 + 1` /\
              `i0 + 1 <= (array_length t0)`) /\
              (sorted_array t0 `i0 + 1` `(array_length t0) - 1`) /\
              (permut t0 t) /\
              ((`i0 + 1 < (array_length t0)` ->
                (Maximize t0 i0 (access t0 `i0 + 1`) `0`))))
              (sig_3 Z (array Z) unit [i1: Z][t1: (array Z)][result0: unit]
               (((`0 <= i1 + 1` /\ `i1 + 1 <= (array_length t1)`) /\
               (sorted_array t1 `i1 + 1` `(array_length t1) - 1`) /\
               (permut t1 t) /\
               ((`i1 + 1 < (array_length t1)` ->
                 (Maximize t1 i1 (access t1 `i1 + 1`) `0`)))) /\
               `i1 < 0`));
              i0: Z; t0: (array Z); Pre9: Variant1 = `i0 + 1`;
              Pre8: (`0 <= i0 + 1` /\ `i0 + 1 <= (array_length t0)`) /\
              (sorted_array t0 `i0 + 1` `(array_length t0) - 1`) /\
              (permut t0 t) /\
              ((`i0 + 1 < (array_length t0)` ->
                (Maximize t0 i0 (access t0 `i0 + 1`) `0`)))]
               let (result0, Bool1) =
                 let (result2, Post6) = (Z_ge_lt_bool i0 `0`) in
                 (exist_1 [result3: bool]
                 (if result3 then `i0 >= 0` else `i0 < 0`) result2 Post6) in
               Cases
                 (btest
                  [result0:bool](if result0 then `i0 >= 0` else `i0 < 0`) result0
                  Bool1) of
               | (left Test2) =>
                   let (i1, t1, result1, Post2) =
                     let (i1, t1, result1, Post4) =
                       let (t1, result1, WP2) =
                         let Pre7 =
                           (maxisort_po_1 t Pre10 result Post3 Variant1 i0 t0
                           Pre9 Pre8 Test2) in
                         let (r, Post7) =
                           let Pre2 = Pre7 in
                           let Pre3 = Pre2 in
                           let (result3, Post8) =
                             (maximum i0 i0 i0 t0 Pre2) in
                           (exist_1 [result4: Z](`0 <= result4` /\
                           `result4 <= i0`) /\
                           (Maximize t0 i0 (access t0 result4) `0`) result3
                           Post8) in
                         let Pre6 =
                           (maxisort_po_2 t Pre10 result Post3 Variant1 i0 t0
                           Pre9 Pre8 Test2 Pre7 r Post7) in
                         let (t1, result1, Post9) =
                           let Pre4 = Pre6 in
                           let Pre5 = Pre4 in
                           let (t1, result3, Post10) = (swap i0 r t0 Pre4) in
                           (exist_2 [t2: (array Z)][result4: unit]
                           (exchange t2 t0 i0 r) t1 result3 Post10) in
                         (exist_2 [t2: (array Z)][result2: unit]
                         ((i:Z)
                          (i = `i0 - 1` -> ((`0 <= i + 1` /\
                           `i + 1 <= (array_length t2)`) /\
                           (sorted_array t2 `i + 1` `(array_length t2) - 1`) /\
                           (permut t2 t) /\
                           ((`i + 1 < (array_length t2)` ->
                             (Maximize t2 i (access t2 `i + 1`) `0`)))) /\
                           (Zwf `0` `i + 1` `i0 + 1`))) t1
                         result1
                         (maxisort_po_3 t Pre10 result Post3 Variant1 i0 t0
                         Pre9 Pre8 Test2 Pre7 r Post7 Pre6 t1 Post9)) in
                       let (i1, result2, Post1) =
                         let (result2, Post1) = (exist_1 [result2: Z]
                           result2 = `i0 - 1` `i0 - 1`
                           (refl_equal ? `i0 - 1`)) in
                         (exist_2 [i2: Z][result3: unit]i2 = `i0 - 1` 
                         result2 tt Post1) in
                       (exist_3 [i2: Z][t2: (array Z)][result3: unit]
                       ((`0 <= i2 + 1` /\ `i2 + 1 <= (array_length t2)`) /\
                       (sorted_array t2 `i2 + 1` `(array_length t2) - 1`) /\
                       (permut t2 t) /\
                       ((`i2 + 1 < (array_length t2)` ->
                         (Maximize t2 i2 (access t2 `i2 + 1`) `0`)))) /\
                       (Zwf `0` `i2 + 1` `i0 + 1`) i1 t1 result2
                       let HW_2 = (WP2 i1 Post1) in
                       HW_2) in
                     ((wf1 `i1 + 1`) (loop_variant_1 Pre9 Post4) i1 t1
                       (refl_equal ? `i1 + 1`) (proj1 ? ? Post4)) in
                   (exist_3 [i2: Z][t2: (array Z)][result2: unit]
                   ((`0 <= i2 + 1` /\ `i2 + 1 <= (array_length t2)`) /\
                   (sorted_array t2 `i2 + 1` `(array_length t2) - 1`) /\
                   (permut t2 t) /\
                   ((`i2 + 1 < (array_length t2)` ->
                     (Maximize t2 i2 (access t2 `i2 + 1`) `0`)))) /\
                   `i2 < 0` i1 t1 result1 Post2)
               | (right Test1) =>
                   let (i1, t1, result1, Post2) = (exist_3 [i1: Z]
                     [t1: (array Z)][result1: unit]((`0 <= i1 + 1` /\
                     `i1 + 1 <= (array_length t1)`) /\
                     (sorted_array t1 `i1 + 1` `(array_length t1) - 1`) /\
                     (permut t1 t) /\
                     ((`i1 + 1 < (array_length t1)` ->
                       (Maximize t1 i1 (access t1 `i1 + 1`) `0`)))) /\
                     `i1 < 0` i0 t0 tt (conj ? ? Pre8 Test1)) in
                   (exist_3 [i2: Z][t2: (array Z)][result2: unit]
                   ((`0 <= i2 + 1` /\ `i2 + 1 <= (array_length t2)`) /\
                   (sorted_array t2 `i2 + 1` `(array_length t2) - 1`) /\
                   (permut t2 t) /\
                   ((`i2 + 1 < (array_length t2)` ->
                     (Maximize t2 i2 (access t2 `i2 + 1`) `0`)))) /\
                   `i2 < 0` i1 t1 result1 Post2) end `result + 1` result 
             t (refl_equal ? `result + 1`)
             (maxisort_po_4 t Pre10 result Post3)) in
         (exist_2 [t1: (array Z)][result1: unit]
         (sorted_array t1 `0` `(array_length t1) - 1`) /\ (permut t1 t) 
         t0 result0 (maxisort_po_5 t Pre10 result Post3 i0 t0 Post2)) in
       (exist_2 [t1: (array Z)][result0: unit]
       (sorted_array t1 `0` `(array_length t1) - 1`) /\ (permut t1 t) 
       t0 result Post5).
