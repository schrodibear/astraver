(* This file is generated by Why; do not edit *)

Require Why.
Require Export bsearch_why.

Definition binary_search (* validation *)
  : (l: Z)(m: Z)(p: Z)(t: (array Z))(u: Z)(_: `(array_length t) >= 1` /\
    (sorted_array t `1` `(array_length t) - 1`))
    (sig_5 Z Z Z Z unit [l0: Z][m0: Z][p0: Z][u0: Z][result: unit]
     ((`1 <= p0` /\ `p0 <= (array_length t) - 1`) /\ `(access t p0) = v` \/
     `p0 = 0` /\ ~(In t `1` `(array_length t) - 1`)))
  := [l: Z; m: Z; p: Z; t: (array Z); u: Z; Pre15: `(array_length t) >= 1` /\
      (sorted_array t `1` `(array_length t) - 1`)]
       let (l0, result, Post1) =
         let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
           (refl_equal ? `1`)) in
         (exist_2 [l1: Z][result0: unit]l1 = `1` result tt Post1) in
       let (u0, result0, Post2) =
         let (result0, Post2) = (exist_1 [result0: Z]
           result0 = `(array_length t) - 1` `(array_length t) - 1`
           (refl_equal ? `(array_length t) - 1`)) in
         (exist_2 [u1: Z][result1: unit]u1 = `(array_length t) - 1` result0
         tt Post2) in
       let (p0, result1, Post3) =
         let (result1, Post3) = (exist_1 [result1: Z]result1 = `0` `0`
           (refl_equal ? `0`)) in
         (exist_2 [p1: Z][result2: unit]p1 = `0` result1 tt Post3) in
       let (l1, m0, p1, u1, result2, Post9) =
         (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
           [Variant1: Z](l1: Z)(m0: Z)(p1: Z)(u1: Z)
           (_: Variant1 = `2 + u1 - l1`)(_0: `1 <= l1` /\
           `u1 <= (array_length t) - 1` /\ (`0 <= p1` /\
           `p1 <= (array_length t) - 1`) /\
           ((`p1 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l1 u1)))) /\
           ((`p1 > 0` -> `(access t p1) = v`)))
           (sig_5 Z Z Z Z unit [l2: Z][m1: Z][p2: Z][u2: Z][result2: unit]
            ((`1 <= l2` /\ `u2 <= (array_length t) - 1` /\ (`0 <= p2` /\
            `p2 <= (array_length t) - 1`) /\
            ((`p2 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l2 u2)))) /\
            ((`p2 > 0` -> `(access t p2) = v`))) /\ `l2 > u2`))
           [Variant1: Z; wf1: (Variant2: Z)
            (Pre1: (Zwf `0` Variant2 Variant1))(l1: Z)(m0: Z)(p1: Z)(u1: Z)
            (_: Variant2 = `2 + u1 - l1`)(_0: `1 <= l1` /\
            `u1 <= (array_length t) - 1` /\ (`0 <= p1` /\
            `p1 <= (array_length t) - 1`) /\
            ((`p1 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l1 u1)))) /\
            ((`p1 > 0` -> `(access t p1) = v`)))
            (sig_5 Z Z Z Z unit [l2: Z][m1: Z][p2: Z][u2: Z][result2: unit]
             ((`1 <= l2` /\ `u2 <= (array_length t) - 1` /\ (`0 <= p2` /\
             `p2 <= (array_length t) - 1`) /\
             ((`p2 = 0` ->
               ((In t `1` `(array_length t) - 1`) -> (In t l2 u2)))) /\
             ((`p2 > 0` -> `(access t p2) = v`))) /\ `l2 > u2`));
            l1: Z; m0: Z; p1: Z; u1: Z; Pre14: Variant1 = `2 + u1 - l1`;
            Pre13: `1 <= l1` /\ `u1 <= (array_length t) - 1` /\ (`0 <= p1` /\
            `p1 <= (array_length t) - 1`) /\
            ((`p1 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l1 u1)))) /\
            ((`p1 > 0` -> `(access t p1) = v`))]
             let (result2, Bool3) =
               let (result4, Post13) = (Z_le_gt_bool l1 u1) in
               (exist_1 [result5: bool]
               (if result5 then `l1 <= u1` else `l1 > u1`) result4 Post13) in
             Cases
               (btest
                [result2:bool](if result2 then `l1 <= u1` else `l1 > u1`) result2
                Bool3) of
             | (left Test6) =>
                 let (l2, m1, p2, u2, result3, Post9) =
                   let (l2, m1, p2, u2, result3, Post10) =
                     let (m1, result3, Post4) =
                       let (result3, Post4) = (exist_1 [result3: Z]
                         result3 = (mean l1 u1) (mean l1 u1)
                         (refl_equal ? (mean l1 u1))) in
                       (exist_2 [m2: Z][result4: unit]
                       m2 = (mean l1 u1) result3 tt Post4) in
                     let Pre12 =
                       (binary_search_po_1 t Pre15 l0 Post1 u0 Post2 p0 Post3
                       Variant1 l1 p1 u1 Pre14 Pre13 Test6 m1 Post4) in
                     let (l2, p2, u2, result4, Post10) =
                       let Pre11 =
                         (binary_search_po_2 t Pre15 l0 Post1 u0 Post2 p0
                         Post3 Variant1 l1 p1 u1 Pre14 Pre13 Test6 m1 Post4
                         Pre12) in
                       let (result4, Bool2) =
                         let Pre5 = Pre11 in
                         let result5 =
                           let Pre3 = Pre5 in
                           let Pre2 = Pre3 in
                           (Z_lt_ge_bool (access t m1)) in
                         let Pre4 = Pre5 in
                         let (result6, Post14) = (result5 v) in
                         (exist_1 [result7: bool]
                         (if result7 then `(access t m1) < v`
                          else `(access t m1) >= v`) result6
                         Post14) in
                       Cases
                         (btest
                          [result4:bool]
                          (if result4 then `(access t m1) < v`
                           else `(access t m1) >= v`) result4
                          Bool2) of
                       | (left Test5) =>
                           let (l2, result5, Post5) =
                             let (result5, Post5) = (exist_1 [result5: Z]
                               result5 = `m1 + 1` `m1 + 1`
                               (refl_equal ? `m1 + 1`)) in
                             (exist_2 [l3: Z][result6: unit]
                             l3 = `m1 + 1` result5 tt Post5) in
                           (exist_4 [l3: Z][p2: Z][u2: Z][result6: unit]
                           (`1 <= l3` /\ `u2 <= (array_length t) - 1` /\
                           (`0 <= p2` /\ `p2 <= (array_length t) - 1`) /\
                           ((`p2 = 0` ->
                             ((In t `1` `(array_length t) - 1`) ->
                              (In t l3 u2)))) /\
                           ((`p2 > 0` -> `(access t p2) = v`))) /\
                           (Zwf `0` `2 + u2 - l3` `2 + u1 - l1`) l2 p1 
                           u1 result5
                           (binary_search_po_3 t Pre15 l0 Post1 u0 Post2 p0
                           Post3 Variant1 l1 p1 u1 Pre14 Pre13 Test6 m1 Post4
                           Pre12 Pre11 Test5 l2 Post5))
                       | (right Test4) =>
                           let (l2, p2, u2, result5, Post10) =
                             let Pre10 = Pre11 in
                             let (result5, Bool1) =
                               let Pre9 = Pre10 in
                               let result6 =
                                 let Pre7 = Pre9 in
                                 let Pre6 = Pre7 in
                                 (Z_gt_le_bool (access t m1)) in
                               let Pre8 = Pre9 in
                               let (result7, Post15) = (result6 v) in
                               (exist_1 [result8: bool]
                               (if result8 then `(access t m1) > v`
                                else `(access t m1) <= v`) result7
                               Post15) in
                             Cases
                               (btest
                                [result5:bool]
                                (if result5 then `(access t m1) > v`
                                 else `(access t m1) <= v`) result5
                                Bool1) of
                             | (left Test3) =>
                                 let (u2, result6, Post6) =
                                   let (result6, Post6) =
                                     (exist_1 [result6: Z]
                                     result6 = `m1 - 1` `m1 - 1`
                                     (refl_equal ? `m1 - 1`)) in
                                   (exist_2 [u3: Z][result7: unit]
                                   u3 = `m1 - 1` result6 tt Post6) in
                                 (exist_4 [l2: Z][p2: Z][u3: Z]
                                 [result7: unit](`1 <= l2` /\
                                 `u3 <= (array_length t) - 1` /\
                                 (`0 <= p2` /\
                                 `p2 <= (array_length t) - 1`) /\
                                 ((`p2 = 0` ->
                                   ((In t `1` `(array_length t) - 1`) ->
                                    (In t l2 u3)))) /\
                                 ((`p2 > 0` -> `(access t p2) = v`))) /\
                                 (Zwf `0` `2 + u3 - l2` `2 + u1 - l1`) 
                                 l1 p1 u2 result6
                                 (binary_search_po_4 t Pre15 l0 Post1 u0
                                 Post2 p0 Post3 Variant1 l1 p1 u1 Pre14 Pre13
                                 Test6 m1 Post4 Pre12 Pre11 Test4 Pre10 Test3
                                 u2 Post6))
                             | (right Test2) =>
                                 let (l2, p2, result6, Post10) =
                                   let (p2, result6, Post7) =
                                     let (result6, Post7) =
                                       (exist_1 [result6: Z]result6 = m1 
                                       m1 (refl_equal ? m1)) in
                                     (exist_2 [p3: Z][result7: unit]
                                     p3 = m1 result6 tt Post7) in
                                   let (l2, result7, Post8) =
                                     let (result7, Post8) =
                                       (exist_1 [result7: Z]
                                       result7 = `u1 + 1` `u1 + 1`
                                       (refl_equal ? `u1 + 1`)) in
                                     (exist_2 [l3: Z][result8: unit]
                                     l3 = `u1 + 1` result7 tt Post8) in
                                   (exist_3 [l3: Z][p3: Z][result8: unit]
                                   (`1 <= l3` /\
                                   `u1 <= (array_length t) - 1` /\
                                   (`0 <= p3` /\
                                   `p3 <= (array_length t) - 1`) /\
                                   ((`p3 = 0` ->
                                     ((In t `1` `(array_length t) - 1`) ->
                                      (In t l3 u1)))) /\
                                   ((`p3 > 0` -> `(access t p3) = v`))) /\
                                   (Zwf `0` `2 + u1 - l3` `2 + u1 - l1`) 
                                   l2 p2 result7
                                   (binary_search_po_5 t Pre15 l0 Post1 u0
                                   Post2 p0 Post3 Variant1 l1 p1 u1 Pre14
                                   Pre13 Test6 m1 Post4 Pre12 Pre11 Test4
                                   Pre10 Test2 p2 Post7 l2 Post8)) in
                                 (exist_4 [l3: Z][p3: Z][u2: Z]
                                 [result7: unit](`1 <= l3` /\
                                 `u2 <= (array_length t) - 1` /\
                                 (`0 <= p3` /\
                                 `p3 <= (array_length t) - 1`) /\
                                 ((`p3 = 0` ->
                                   ((In t `1` `(array_length t) - 1`) ->
                                    (In t l3 u2)))) /\
                                 ((`p3 > 0` -> `(access t p3) = v`))) /\
                                 (Zwf `0` `2 + u2 - l3` `2 + u1 - l1`) 
                                 l2 p2 u1 result6 Post10) end in
                           (exist_4 [l3: Z][p3: Z][u3: Z][result6: unit]
                           (`1 <= l3` /\ `u3 <= (array_length t) - 1` /\
                           (`0 <= p3` /\ `p3 <= (array_length t) - 1`) /\
                           ((`p3 = 0` ->
                             ((In t `1` `(array_length t) - 1`) ->
                              (In t l3 u3)))) /\
                           ((`p3 > 0` -> `(access t p3) = v`))) /\
                           (Zwf `0` `2 + u3 - l3` `2 + u1 - l1`) l2 p2 
                           u2 result5 Post10) end in
                     (exist_5 [l3: Z][m2: Z][p3: Z][u3: Z][result5: unit]
                     (`1 <= l3` /\ `u3 <= (array_length t) - 1` /\
                     (`0 <= p3` /\ `p3 <= (array_length t) - 1`) /\
                     ((`p3 = 0` ->
                       ((In t `1` `(array_length t) - 1`) -> (In t l3 u3)))) /\
                     ((`p3 > 0` -> `(access t p3) = v`))) /\
                     (Zwf `0` `2 + u3 - l3` `2 + u1 - l1`) l2 m1 p2 u2
                     result4 Post10) in
                   ((wf1 `2 + u2 - l2`) (loop_variant_1 Pre14 Post10) 
                     l2 m1 p2 u2 (refl_equal ? `2 + u2 - l2`)
                     (proj1 ? ? Post10)) in
                 (exist_5 [l3: Z][m2: Z][p3: Z][u3: Z][result4: unit]
                 (`1 <= l3` /\ `u3 <= (array_length t) - 1` /\ (`0 <= p3` /\
                 `p3 <= (array_length t) - 1`) /\
                 ((`p3 = 0` ->
                   ((In t `1` `(array_length t) - 1`) -> (In t l3 u3)))) /\
                 ((`p3 > 0` -> `(access t p3) = v`))) /\ `l3 > u3` l2 
                 m1 p2 u2 result3 Post9)
             | (right Test1) =>
                 let (l2, m1, p2, u2, result3, Post9) = (exist_5 [l2: Z]
                   [m1: Z][p2: Z][u2: Z][result3: unit](`1 <= l2` /\
                   `u2 <= (array_length t) - 1` /\ (`0 <= p2` /\
                   `p2 <= (array_length t) - 1`) /\
                   ((`p2 = 0` ->
                     ((In t `1` `(array_length t) - 1`) -> (In t l2 u2)))) /\
                   ((`p2 > 0` -> `(access t p2) = v`))) /\ `l2 > u2` 
                   l1 m0 p1 u1 tt (conj ? ? Pre13 Test1)) in
                 (exist_5 [l3: Z][m2: Z][p3: Z][u3: Z][result4: unit]
                 (`1 <= l3` /\ `u3 <= (array_length t) - 1` /\ (`0 <= p3` /\
                 `p3 <= (array_length t) - 1`) /\
                 ((`p3 = 0` ->
                   ((In t `1` `(array_length t) - 1`) -> (In t l3 u3)))) /\
                 ((`p3 > 0` -> `(access t p3) = v`))) /\ `l3 > u3` l2 
                 m1 p2 u2 result3 Post9) end `2 + u0 - l0` l0 m p0 u0
           (refl_equal ? `2 + u0 - l0`)
           (binary_search_po_6 t Pre15 l0 Post1 u0 Post2 p0 Post3)) in
       (exist_5 [l2: Z][m1: Z][p2: Z][u2: Z][result3: unit](`1 <= p2` /\
       `p2 <= (array_length t) - 1`) /\ `(access t p2) = v` \/ `p2 = 0` /\
       ~(In t `1` `(array_length t) - 1`) l1 m0 p1 u1 result2
       (binary_search_po_7 t Pre15 l0 Post1 u0 Post2 p0 Post3 l1 p1 u1 Post9)).

