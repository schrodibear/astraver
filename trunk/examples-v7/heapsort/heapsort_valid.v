(* This file is generated by Why; do not edit *)

Require Why.
Require Export swap_valid.
Require Export downheap_valid.
Require Export heapsort_why.

Definition heapsort (* validation *)
  : (t: (array Z))(_: `1 <= (array_length t)`)
    (sig_2 (array Z) unit [t0: (array Z)][result: unit]
     ((sorted_array t0 `0` `(array_length t0) - 1`) /\ (permut t0 t)))
  := [t: (array Z); Pre16: `1 <= (array_length t)`]
       let (t0, result, Post9) =
         let (result, Post3) = (exist_1 [result: Z]
           result = (Zdiv2 `(array_length t) - 2`) (Zdiv2 `(array_length t) -
                                                           2`)
           (refl_equal ? (Zdiv2 `(array_length t) - 2`))) in
         let (k0, t0, result0, Post2) =
           (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
             [Variant1: Z](k0: Z)(t0: (array Z))(_: Variant1 = `k0 + 1`)
             (_0: (`(-1) <= k0` /\ `k0 <= (array_length t0) - 1`) /\
             ((i:Z)
              (`k0 + 1 <= i` /\ `i <= (array_length t0) - 1` ->
               (heap t0 `(array_length t0) - 1` i))) /\ (permut t0 t))
             (sig_3 Z (array Z) unit [k1: Z][t1: (array Z)][result0: unit]
              (((`(-1) <= k1` /\ `k1 <= (array_length t1) - 1`) /\
              ((i:Z)
               (`k1 + 1 <= i` /\ `i <= (array_length t1) - 1` ->
                (heap t1 `(array_length t1) - 1` i))) /\
              (permut t1 t)) /\ `k1 < 0`))
             [Variant1: Z; wf1: (Variant2: Z)
              (Pre1: (Zwf `0` Variant2 Variant1))(k0: Z)(t0: (array Z))
              (_: Variant2 = `k0 + 1`)(_0: (`(-1) <= k0` /\
              `k0 <= (array_length t0) - 1`) /\
              ((i:Z)
               (`k0 + 1 <= i` /\ `i <= (array_length t0) - 1` ->
                (heap t0 `(array_length t0) - 1` i))) /\
              (permut t0 t))
              (sig_3 Z (array Z) unit [k1: Z][t1: (array Z)][result0: unit]
               (((`(-1) <= k1` /\ `k1 <= (array_length t1) - 1`) /\
               ((i:Z)
                (`k1 + 1 <= i` /\ `i <= (array_length t1) - 1` ->
                 (heap t1 `(array_length t1) - 1` i))) /\
               (permut t1 t)) /\ `k1 < 0`));
              k0: Z; t0: (array Z); Pre6: Variant1 = `k0 + 1`;
              Pre5: (`(-1) <= k0` /\ `k0 <= (array_length t0) - 1`) /\
              ((i:Z)
               (`k0 + 1 <= i` /\ `i <= (array_length t0) - 1` ->
                (heap t0 `(array_length t0) - 1` i))) /\
              (permut t0 t)]
               let (result0, Bool1) =
                 let (result2, Post10) = (Z_ge_lt_bool k0 `0`) in
                 (exist_1 [result3: bool]
                 (if result3 then `k0 >= 0` else `k0 < 0`) result2 Post10) in
               Cases
                 (btest
                  [result0:bool](if result0 then `k0 >= 0` else `k0 < 0`) result0
                  Bool1) of
               | (left Test2) =>
                   let (k1, t1, result1, Post2) =
                     let (k1, t1, result1, Post8) =
                       let Pre4 =
                         (heapsort_po_1 t Pre16 result Post3 Variant1 k0 t0
                         Pre6 Pre5 Test2) in
                       let (t1, result1, Post11) =
                         let Pre2 = Pre4 in
                         let Pre3 = Pre2 in
                         let (t1, result3, Post12) =
                           (downheap k0 `(array_length t0) - 1` t0 Pre2) in
                         (exist_2 [t2: (array Z)][result4: unit]
                         (permut t2 t0) /\
                         ((i:Z)
                          (`k0 <= i` /\ `i <= (array_length t0) - 1` ->
                           (heap t2 `(array_length t0) - 1` i))) /\
                         ((i:Z)
                          (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                           `i < 2 * k0 + 1` \/ `(array_length t0) - 1 < i` /\
                           `i < (array_length t2)` ->
                           `(access t2 i) = (access t0 i)`)) /\
                         ((v:Z)
                          ((inftree t0 `(array_length t0) - 1` v k0) ->
                           (inftree t2 `(array_length t0) - 1` v k0))) 
                         t1 result3 Post12) in
                       let (k1, result2, Post1) =
                         let (result2, Post1) = (exist_1 [result2: Z]
                           result2 = `k0 - 1` `k0 - 1`
                           (refl_equal ? `k0 - 1`)) in
                         (exist_2 [k2: Z][result3: unit]k2 = `k0 - 1` 
                         result2 tt Post1) in
                       (exist_3 [k2: Z][t2: (array Z)][result3: unit]
                       ((`(-1) <= k2` /\ `k2 <= (array_length t2) - 1`) /\
                       ((i:Z)
                        (`k2 + 1 <= i` /\ `i <= (array_length t2) - 1` ->
                         (heap t2 `(array_length t2) - 1` i))) /\
                       (permut t2 t)) /\ (Zwf `0` `k2 + 1` `k0 + 1`) 
                       k1 t1 result2
                       (heapsort_po_2 t Pre16 result Post3 Variant1 k0 t0
                       Pre6 Pre5 Test2 Pre4 t1 Post11 k1 Post1)) in
                     ((wf1 `k1 + 1`) (loop_variant_1 Pre6 Post8) k1 t1
                       (refl_equal ? `k1 + 1`) (proj1 ? ? Post8)) in
                   (exist_3 [k2: Z][t2: (array Z)][result2: unit]
                   ((`(-1) <= k2` /\ `k2 <= (array_length t2) - 1`) /\
                   ((i:Z)
                    (`k2 + 1 <= i` /\ `i <= (array_length t2) - 1` ->
                     (heap t2 `(array_length t2) - 1` i))) /\
                   (permut t2 t)) /\ `k2 < 0` k1 t1 result1 Post2)
               | (right Test1) =>
                   let (k1, t1, result1, Post2) = (exist_3 [k1: Z]
                     [t1: (array Z)][result1: unit]((`(-1) <= k1` /\
                     `k1 <= (array_length t1) - 1`) /\
                     ((i:Z)
                      (`k1 + 1 <= i` /\ `i <= (array_length t1) - 1` ->
                       (heap t1 `(array_length t1) - 1` i))) /\
                     (permut t1 t)) /\ `k1 < 0` k0 t0 tt
                     (conj ? ? Pre5 Test1)) in
                   (exist_3 [k2: Z][t2: (array Z)][result2: unit]
                   ((`(-1) <= k2` /\ `k2 <= (array_length t2) - 1`) /\
                   ((i:Z)
                    (`k2 + 1 <= i` /\ `i <= (array_length t2) - 1` ->
                     (heap t2 `(array_length t2) - 1` i))) /\
                   (permut t2 t)) /\ `k2 < 0` k1 t1 result1 Post2) end
             `result + 1` result t (refl_equal ? `result + 1`)
             (heapsort_po_3 t Pre16 result Post3)) in
         (exist_2 [t1: (array Z)][result1: unit]
         (heap t1 `(array_length t1) - 1` `0`) /\ (permut t1 t) t0 result0
         (heapsort_po_4 t Pre16 result Post3 k0 t0 Post2)) in
       let (t1, result0, Post13) =
         let (result0, Post6) = (exist_1 [result0: Z]
           result0 = `(array_length t0) - 1` `(array_length t0) - 1`
           (refl_equal ? `(array_length t0) - 1`)) in
         let (k0, t1, result1, Post5) =
           (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
             [Variant3: Z](k0: Z)(t1: (array Z))(_: Variant3 = k0)
             (_0: (`0 <= k0` /\ `k0 <= (array_length t1) - 1`) /\
             ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
             ((`k0 + 1 <= (array_length t1) - 1` ->
               `(access t1 0) <= (access t1 k0 + 1)`)) /\
             ((`k0 + 1 <= (array_length t1) - 1` ->
               (sorted_array t1 `k0 + 1` `(array_length t1) - 1`))) /\
             (permut t1 t))
             (sig_3 Z (array Z) unit [k1: Z][t2: (array Z)][result1: unit]
              (((`0 <= k1` /\ `k1 <= (array_length t2) - 1`) /\
              ((i:Z) (`0 <= i` /\ `i <= k1` -> (heap t2 k1 i))) /\
              ((`k1 + 1 <= (array_length t2) - 1` ->
                `(access t2 0) <= (access t2 k1 + 1)`)) /\
              ((`k1 + 1 <= (array_length t2) - 1` ->
                (sorted_array t2 `k1 + 1` `(array_length t2) - 1`))) /\
              (permut t2 t)) /\ `k1 < 1`))
             [Variant3: Z; wf2: (Variant4: Z)
              (Pre7: (Zwf `0` Variant4 Variant3))(k0: Z)(t1: (array Z))
              (_: Variant4 = k0)(_0: (`0 <= k0` /\
              `k0 <= (array_length t1) - 1`) /\
              ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
              ((`k0 + 1 <= (array_length t1) - 1` ->
                `(access t1 0) <= (access t1 k0 + 1)`)) /\
              ((`k0 + 1 <= (array_length t1) - 1` ->
                (sorted_array t1 `k0 + 1` `(array_length t1) - 1`))) /\
              (permut t1 t))
              (sig_3 Z (array Z) unit [k1: Z][t2: (array Z)][result1: unit]
               (((`0 <= k1` /\ `k1 <= (array_length t2) - 1`) /\
               ((i:Z) (`0 <= i` /\ `i <= k1` -> (heap t2 k1 i))) /\
               ((`k1 + 1 <= (array_length t2) - 1` ->
                 `(access t2 0) <= (access t2 k1 + 1)`)) /\
               ((`k1 + 1 <= (array_length t2) - 1` ->
                 (sorted_array t2 `k1 + 1` `(array_length t2) - 1`))) /\
               (permut t2 t)) /\ `k1 < 1`));
              k0: Z; t1: (array Z); Pre15: Variant3 = k0;
              Pre14: (`0 <= k0` /\ `k0 <= (array_length t1) - 1`) /\
              ((i:Z) (`0 <= i` /\ `i <= k0` -> (heap t1 k0 i))) /\
              ((`k0 + 1 <= (array_length t1) - 1` ->
                `(access t1 0) <= (access t1 k0 + 1)`)) /\
              ((`k0 + 1 <= (array_length t1) - 1` ->
                (sorted_array t1 `k0 + 1` `(array_length t1) - 1`))) /\
              (permut t1 t)]
               let (result1, Bool2) =
                 let (result3, Post14) = (Z_ge_lt_bool k0 `1`) in
                 (exist_1 [result4: bool]
                 (if result4 then `k0 >= 1` else `k0 < 1`) result3 Post14) in
               Cases
                 (btest
                  [result1:bool](if result1 then `k0 >= 1` else `k0 < 1`) result1
                  Bool2) of
               | (left Test4) =>
                   let (k1, t2, result2, Post5) =
                     let (k1, t2, result2, Post7) =
                       let Pre13 =
                         (heapsort_po_5 t Pre16 t0 Post9 result0 Post6
                         Variant3 k0 t1 Pre15 Pre14 Test4) in
                       let (t2, result2, Post15) =
                         let Pre8 = Pre13 in
                         let Pre9 = Pre8 in
                         let (t2, result4, Post16) = (swap `0` k0 t1 Pre8) in
                         (exist_2 [t3: (array Z)][result5: unit]
                         (exchange t3 t1 `0` k0) t2 result4 Post16) in
                       let Pre12 =
                         (heapsort_po_6 t Pre16 t0 Post9 result0 Post6
                         Variant3 k0 t1 Pre15 Pre14 Test4 Pre13 t2 Post15) in
                       let (t3, result3, Post17) =
                         let Pre10 = Pre12 in
                         let Pre11 = Pre10 in
                         let (t3, result5, Post18) =
                           (downheap `0` `k0 - 1` t2 Pre10) in
                         (exist_2 [t4: (array Z)][result6: unit]
                         (permut t4 t2) /\
                         ((i:Z)
                          (`0 <= i` /\ `i <= k0 - 1` -> (heap t4 `k0 - 1` i))) /\
                         ((i:Z)
                          (`0 <= i` /\ `i < 0` \/ `0 < i` /\
                           `i < 2 * 0 + 1` \/ `k0 - 1 < i` /\
                           `i < (array_length t4)` ->
                           `(access t4 i) = (access t2 i)`)) /\
                         ((v:Z)
                          ((inftree t2 `k0 - 1` v `0`) ->
                           (inftree t4 `k0 - 1` v `0`))) t3
                         result5 Post18) in
                       let (k1, result4, Post4) =
                         let (result4, Post4) = (exist_1 [result4: Z]
                           result4 = `k0 - 1` `k0 - 1`
                           (refl_equal ? `k0 - 1`)) in
                         (exist_2 [k2: Z][result5: unit]k2 = `k0 - 1` 
                         result4 tt Post4) in
                       (exist_3 [k2: Z][t4: (array Z)][result5: unit]
                       ((`0 <= k2` /\ `k2 <= (array_length t4) - 1`) /\
                       ((i:Z) (`0 <= i` /\ `i <= k2` -> (heap t4 k2 i))) /\
                       ((`k2 + 1 <= (array_length t4) - 1` ->
                         `(access t4 0) <= (access t4 k2 + 1)`)) /\
                       ((`k2 + 1 <= (array_length t4) - 1` ->
                         (sorted_array t4 `k2 + 1` `(array_length t4) - 1`))) /\
                       (permut t4 t)) /\ (Zwf `0` k2 k0) k1 t3 result4
                       (heapsort_po_7 t Pre16 t0 Post9 result0 Post6 Variant3
                       k0 t1 Pre15 Pre14 Test4 Pre13 t2 Post15 Pre12 t3
                       Post17 k1 Post4)) in
                     ((wf2 k1) (loop_variant_1 Pre15 Post7) k1 t2
                       (refl_equal ? k1) (proj1 ? ? Post7)) in
                   (exist_3 [k2: Z][t3: (array Z)][result3: unit]
                   ((`0 <= k2` /\ `k2 <= (array_length t3) - 1`) /\
                   ((i:Z) (`0 <= i` /\ `i <= k2` -> (heap t3 k2 i))) /\
                   ((`k2 + 1 <= (array_length t3) - 1` ->
                     `(access t3 0) <= (access t3 k2 + 1)`)) /\
                   ((`k2 + 1 <= (array_length t3) - 1` ->
                     (sorted_array t3 `k2 + 1` `(array_length t3) - 1`))) /\
                   (permut t3 t)) /\ `k2 < 1` k1 t2 result2 Post5)
               | (right Test3) =>
                   let (k1, t2, result2, Post5) = (exist_3 [k1: Z]
                     [t2: (array Z)][result2: unit]((`0 <= k1` /\
                     `k1 <= (array_length t2) - 1`) /\
                     ((i:Z) (`0 <= i` /\ `i <= k1` -> (heap t2 k1 i))) /\
                     ((`k1 + 1 <= (array_length t2) - 1` ->
                       `(access t2 0) <= (access t2 k1 + 1)`)) /\
                     ((`k1 + 1 <= (array_length t2) - 1` ->
                       (sorted_array t2 `k1 + 1` `(array_length t2) - 1`))) /\
                     (permut t2 t)) /\ `k1 < 1` k0 t1 tt
                     (conj ? ? Pre14 Test3)) in
                   (exist_3 [k2: Z][t3: (array Z)][result3: unit]
                   ((`0 <= k2` /\ `k2 <= (array_length t3) - 1`) /\
                   ((i:Z) (`0 <= i` /\ `i <= k2` -> (heap t3 k2 i))) /\
                   ((`k2 + 1 <= (array_length t3) - 1` ->
                     `(access t3 0) <= (access t3 k2 + 1)`)) /\
                   ((`k2 + 1 <= (array_length t3) - 1` ->
                     (sorted_array t3 `k2 + 1` `(array_length t3) - 1`))) /\
                   (permut t3 t)) /\ `k2 < 1` k1 t2 result2 Post5) end
             result0 result0 t0 (refl_equal ? result0)
             (heapsort_po_8 t Pre16 t0 Post9 result0 Post6)) in
         (exist_2 [t2: (array Z)][result2: unit]
         (sorted_array t2 `0` `(array_length t2) - 1`) /\ (permut t2 t) 
         t1 result1
         (heapsort_po_9 t Pre16 t0 Post9 result0 Post6 k0 t1 Post5)) in
       (exist_2 [t2: (array Z)][result1: unit]
       (sorted_array t2 `0` `(array_length t2) - 1`) /\ (permut t2 t) 
       t1 result0 Post13).

