(* This file is generated by Why; do not edit *)

Require Why.
Require Export swap_valid.
Require Export downheap_why.

Definition downheap (* validation *)
  : (k: Z)(n: Z)(t: (array Z))(_: (`0 <= k` /\ `k <= n`) /\
    `n < (array_length t)` /\
    ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i))))
    (sig_2 (array Z) unit [t0: (array Z)][result: unit]((permut t0 t) /\
     ((i:Z) (`k <= i` /\ `i <= n` -> (heap t0 n i))) /\
     ((i:Z)
      (`0 <= i` /\ `i < k` \/ `k < i` /\ `i < 2 * k + 1` \/ `n < i` /\
       `i < (array_length t0)` -> `(access t0 i) = (access t i)`)) /\
     ((v:Z) ((inftree t n v k) -> (inftree t0 n v k)))))
  := [k: Z; n: Z; t: (array Z); Pre15: (`0 <= k` /\ `k <= n`) /\
      `n < (array_length t)` /\
      ((i:Z) (`k + 1 <= i` /\ `i <= n` -> (heap t n i)))]
       (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
         [Variant1: Z](k0: Z)(n0: Z)(t0: (array Z))(_: Variant1 = `n0 - k0`)
         (_0: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
         ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
         (sig_2 (array Z) unit [t1: (array Z)][result: unit]
          ((permut t1 t0) /\
          ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t1 n0 i))) /\
          ((i:Z)
           (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
            `n0 < i` /\ `i < (array_length t1)` ->
            `(access t1 i) = (access t0 i)`)) /\
          ((v:Z) ((inftree t0 n0 v k0) -> (inftree t1 n0 v k0)))))
         [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
          (k0: Z)(n0: Z)(t0: (array Z))(_: Variant2 = `n0 - k0`)
          (_0: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i))))
          (sig_2 (array Z) unit [t1: (array Z)][result: unit]
           ((permut t1 t0) /\
           ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t1 n0 i))) /\
           ((i:Z)
            (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
             `n0 < i` /\ `i < (array_length t1)` ->
             `(access t1 i) = (access t0 i)`)) /\
           ((v:Z) ((inftree t0 n0 v k0) -> (inftree t1 n0 v k0)))));
          k0: Z; n0: Z; t0: (array Z); Pre14: Variant1 = `n0 - k0`;
          Pre13: (`0 <= k0` /\ `k0 <= n0`) /\ `n0 < (array_length t0)` /\
          ((i:Z) (`k0 + 1 <= i` /\ `i <= n0` -> (heap t0 n0 i)))]
           let (j, Post3) = (exist_1 [result: Z]
             result = `2 * k0 + 1` `2 * k0 + 1`
             (refl_equal ? `2 * k0 + 1`)) in
           let (t1, result, Post8) =
             let (result, Bool12) =
               let (result1, Post9) = (Z_le_gt_bool j n0) in
               (exist_1 [result2: bool]
               (if result2 then `j <= n0` else `j > n0`) result1 Post9) in
             Cases
               (btest
                [result:bool](if result then `j <= n0` else `j > n0`) result
                Bool12) of
             | (left Test8) =>
                 let (t1, result0, Post11) =
                   let (j', Post12) =
                     let (result0, Bool10) =
                       let (result2, Post13) = (Z_le_gt_bool `j + 1` n0) in
                       (exist_1 [result3: bool]
                       (if result3 then `j + 1 <= n0` else `j + 1 > n0`) 
                       result2 Post13) in
                     Cases
                       (btest
                        [result0:bool]
                        (if result0 then `j + 1 <= n0` else `j + 1 > n0`) result0
                        Bool10) of
                     | (left Test5) =>
                         let (result1, Post15) =
                           let (result1, Bool9) =
                             let Pre3 =
                               (downheap_po_1 k n t Pre15 Variant1 k0 n0 t0
                               Pre14 Pre13 j Post3 Test8 Test5) in
                             let result2 =
                               let Pre2 =
                                 (downheap_po_2 k n t Pre15 Variant1 k0 n0 t0
                                 Pre14 Pre13 j Post3 Test8 Test5 Pre3) in
                               (Z_lt_ge_bool (access t0 j)) in
                             let (result3, Post16) =
                               (result2 (access t0 `j + 1`)) in
                             (exist_1 [result4: bool]
                             (if result4
                              then `(access t0 j) < (access t0 j + 1)`
                              else `(access t0 j) >= (access t0 j + 1)`) 
                             result3 Post16) in
                           Cases
                             (btest
                              [result1:bool]
                              (if result1
                               then `(access t0 j) < (access t0 j + 1)`
                               else `(access t0 j) >= (access t0 j + 1)`) result1
                              Bool9) of
                           | (left Test4) =>
                               let (result2, Post18) = (exist_1 [result2: Z]
                                 (select_son t0 k0 n0 result2) `j + 1`
                                 (downheap_po_3 k n t Pre15 Variant1 k0 n0 t0
                                 Pre14 Pre13 j Post3 Test8 Test5 Test4)) in
                               (exist_1 [result3: Z]
                               (select_son t0 k0 n0 result3) result2 Post18)
                           | (right Test3) =>
                               let (result2, Post17) = (exist_1 [result2: Z]
                                 (select_son t0 k0 n0 result2) j
                                 (downheap_po_4 k n t Pre15 Variant1 k0 n0 t0
                                 Pre14 Pre13 j Post3 Test8 Test5 Test3)) in
                               (exist_1 [result3: Z]
                               (select_son t0 k0 n0 result3) result2 Post17) end in
                         (exist_1 [result2: Z]
                         (select_son t0 k0 n0 result2) result1 Post15)
                     | (right Test2) =>
                         let (result1, Post14) = (exist_1 [result1: Z]
                           (select_son t0 k0 n0 result1) j
                           (downheap_po_5 k n t Pre15 Variant1 k0 n0 t0 Pre14
                           Pre13 j Post3 Test8 Test2)) in
                         (exist_1 [result2: Z]
                         (select_son t0 k0 n0 result2) result1 Post14) end in
                   let (t1, result0, Post19) =
                     let (result0, Bool11) =
                       let Pre5 =
                         (downheap_po_6 k n t Pre15 Variant1 k0 n0 t0 Pre14
                         Pre13 j Post3 Test8 j' Post12) in
                       let result1 =
                         let Pre4 =
                           (downheap_po_7 k n t Pre15 Variant1 k0 n0 t0 Pre14
                           Pre13 j Post3 Test8 j' Post12 Pre5) in
                         (Z_lt_ge_bool (access t0 k0)) in
                       let (result2, Post20) = (result1 (access t0 j')) in
                       (exist_1 [result3: bool]
                       (if result3 then `(access t0 k0) < (access t0 j')`
                        else `(access t0 k0) >= (access t0 j')`) result2
                       Post20) in
                     Cases
                       (btest
                        [result0:bool]
                        (if result0 then `(access t0 k0) < (access t0 j')`
                         else `(access t0 k0) >= (access t0 j')`) result0
                        Bool11) of
                     | (left Test7) =>
                         let (t1, result1, Post22) =
                           let Pre12 =
                             (downheap_po_8 k n t Pre15 Variant1 k0 n0 t0
                             Pre14 Pre13 j Post3 Test8 j' Post12 Test7) in
                           let (t1, result1, Post23) =
                             let Pre6 = Pre12 in
                             let Pre7 = Pre6 in
                             let (t1, result3, Post24) =
                               (swap k0 j' t0 Pre6) in
                             (exist_2 [t2: (array Z)][result4: unit]
                             (exchange t2 t0 k0 j') t1 result3 Post24) in
                           let Pre11 =
                             (downheap_po_9 k n t Pre15 Variant1 k0 n0 t0
                             Pre14 Pre13 j Post3 Test8 j' Post12 Test7 Pre12
                             t1 Post23) in
                           let (t2, result2, Post25) =
                             let Pre9 = Pre11 in
                             let Pre10 = Pre9 in
                             let (t2, result4, Post26) =
                               ((wf1 `n0 - j'`)
                                 (downheap_po_10 k n t Pre15 Variant1 k0 n0
                                 t0 Pre14 Pre13 j Post3 Test8 j' Post12 Test7
                                 Pre12 t1 Post23 Pre11 Pre9 Pre10) j' 
                                 n0 t1 (refl_equal ? `n0 - j'`)
                                 (downheap_po_11 k n t Pre15 Variant1 k0 n0
                                 t0 Pre14 Pre13 j Post3 Test8 j' Post12 Test7
                                 Pre12 t1 Post23 Pre11 Pre9 Pre10)) in
                             (exist_2 [t3: (array Z)][result5: unit]
                             (permut t3 t1) /\
                             ((i:Z)
                              (`j' <= i` /\ `i <= n0` -> (heap t3 n0 i))) /\
                             ((i:Z)
                              (`0 <= i` /\ `i < j'` \/ `j' < i` /\
                               `i < 2 * j' + 1` \/ `n0 < i` /\
                               `i < (array_length t3)` ->
                               `(access t3 i) = (access t1 i)`)) /\
                             ((v:Z)
                              ((inftree t1 n0 v j') -> (inftree t3 n0 v j'))) 
                             t2 result4 Post26) in
                           (exist_2 [t3: (array Z)][result3: unit]
                           (permut t3 t0) /\
                           ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t3 n0 i))) /\
                           ((i:Z)
                            (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                             `i < 2 * k0 + 1` \/ `n0 < i` /\
                             `i < (array_length t3)` ->
                             `(access t3 i) = (access t0 i)`)) /\
                           ((v:Z)
                            ((inftree t0 n0 v k0) -> (inftree t3 n0 v k0))) 
                           t2 result2
                           (downheap_po_12 k n t Pre15 Variant1 k0 n0 t0
                           Pre14 Pre13 j Post3 Test8 j' Post12 Test7 Pre12 t1
                           Post23 Pre11 t2 Post25)) in
                         (exist_2 [t2: (array Z)][result2: unit]
                         (permut t2 t0) /\
                         ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
                         ((i:Z)
                          (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                           `i < 2 * k0 + 1` \/ `n0 < i` /\
                           `i < (array_length t2)` ->
                           `(access t2 i) = (access t0 i)`)) /\
                         ((v:Z)
                          ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))) 
                         t1 result1 Post22)
                     | (right Test6) =>
                         let (result1, Post21) = (exist_1 [result1: unit]
                           (permut t0 t0) /\
                           ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t0 n0 i))) /\
                           ((i:Z)
                            (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                             `i < 2 * k0 + 1` \/ `n0 < i` /\
                             `i < (array_length t0)` ->
                             `(access t0 i) = (access t0 i)`)) /\
                           ((v:Z)
                            ((inftree t0 n0 v k0) -> (inftree t0 n0 v k0))) 
                           tt
                           (downheap_po_13 k n t Pre15 Variant1 k0 n0 t0
                           Pre14 Pre13 j Post3 Test8 j' Post12 Test6)) in
                         (exist_2 [t1: (array Z)][result2: unit]
                         (permut t1 t0) /\
                         ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t1 n0 i))) /\
                         ((i:Z)
                          (`0 <= i` /\ `i < k0` \/ `k0 < i` /\
                           `i < 2 * k0 + 1` \/ `n0 < i` /\
                           `i < (array_length t1)` ->
                           `(access t1 i) = (access t0 i)`)) /\
                         ((v:Z)
                          ((inftree t0 n0 v k0) -> (inftree t1 n0 v k0))) 
                         t0 result1 Post21) end in
                   (exist_2 [t2: (array Z)][result1: unit](permut t2 t0) /\
                   ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
                   ((i:Z)
                    (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
                     `n0 < i` /\ `i < (array_length t2)` ->
                     `(access t2 i) = (access t0 i)`)) /\
                   ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))) 
                   t1 result0 Post19) in
                 (exist_2 [t2: (array Z)][result1: unit](permut t2 t0) /\
                 ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
                 ((i:Z)
                  (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
                   `n0 < i` /\ `i < (array_length t2)` ->
                   `(access t2 i) = (access t0 i)`)) /\
                 ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))) 
                 t1 result0 Post11)
             | (right Test1) =>
                 let (result0, Post10) = (exist_1 [result0: unit]
                   (permut t0 t0) /\
                   ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t0 n0 i))) /\
                   ((i:Z)
                    (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
                     `n0 < i` /\ `i < (array_length t0)` ->
                     `(access t0 i) = (access t0 i)`)) /\
                   ((v:Z) ((inftree t0 n0 v k0) -> (inftree t0 n0 v k0))) 
                   tt
                   (downheap_po_14 k n t Pre15 Variant1 k0 n0 t0 Pre14 Pre13
                   j Post3 Test1)) in
                 (exist_2 [t1: (array Z)][result1: unit](permut t1 t0) /\
                 ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t1 n0 i))) /\
                 ((i:Z)
                  (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
                   `n0 < i` /\ `i < (array_length t1)` ->
                   `(access t1 i) = (access t0 i)`)) /\
                 ((v:Z) ((inftree t0 n0 v k0) -> (inftree t1 n0 v k0))) 
                 t0 result0 Post10) end in
           (exist_2 [t2: (array Z)][result0: unit](permut t2 t0) /\
           ((i:Z) (`k0 <= i` /\ `i <= n0` -> (heap t2 n0 i))) /\
           ((i:Z)
            (`0 <= i` /\ `i < k0` \/ `k0 < i` /\ `i < 2 * k0 + 1` \/
             `n0 < i` /\ `i < (array_length t2)` ->
             `(access t2 i) = (access t0 i)`)) /\
           ((v:Z) ((inftree t0 n0 v k0) -> (inftree t2 n0 v k0))) t1 
           result Post8) `n - k` k n t (refl_equal ? `n - k`) Pre15).

