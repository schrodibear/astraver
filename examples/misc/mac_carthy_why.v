(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

Definition max : Z->Z->Z := 
  [x,y] Cases (Z_le_gt_dec x y) of (left _) => y | (right _) => x end.

(* Why obligation from file "mac_carthy.mlw", characters 122-254 *)
Lemma f91_po_1 : 
  (Variant1: Z)
  (n0: Z)
  (Pre2: Variant1 = (max `0` `101 - n0`))
  (Test2: `n0 <= 100`)
  (Zwf `0` (max `0` `101 - (n0 + 11)`) Variant1).
Proof.
Intros Variant1 n. Unfold Zwf max.
Case (Z_le_gt_dec `0` `101-n`); Intros Pre2 Test2;
Case (Z_le_gt_dec `0` `101-(n+11)`); Intuition; Omega.
Save.

(* Why obligation from file "mac_carthy.mlw", characters 122-254 *)
Lemma f91_po_2 : 
  (Variant1: Z)
  (n0: Z)
  (Pre2: Variant1 = (max `0` `101 - n0`))
  (Test2: `n0 <= 100`)
  (aux_3: Z)
  (Post5: `n0 + 11 <= 100` /\ `aux_3 = 91` \/ `n0 + 11 >= 101` /\
          `aux_3 = n0 + 11 - 10`)
  (Zwf `0` (max `0` `101 - aux_3`) Variant1).
Proof.
Intros Variant1 n. Unfold Zwf max.
Case (Z_le_gt_dec `0` `101-n`); Intros H Pre2 Test2 aux_1 Post5;
Case (Z_le_gt_dec `0` `101-aux_1`); Intuition Omega.
Save.

(* Why obligation from file "mac_carthy.mlw", characters 149-169 *)
Lemma f91_po_3 : 
  (Variant1: Z)
  (n0: Z)
  (Pre2: Variant1 = (max `0` `101 - n0`))
  (Test2: `n0 <= 100`)
  (aux_3: Z)
  (Post5: `n0 + 11 <= 100` /\ `aux_3 = 91` \/ `n0 + 11 >= 101` /\
          `aux_3 = n0 + 11 - 10`)
  (result0: Z)
  (Post7: `aux_3 <= 100` /\ `result0 = 91` \/ `aux_3 >= 101` /\
          `result0 = aux_3 - 10`)
  `n0 <= 100` /\ `result0 = 91` \/ `n0 >= 101` /\ `result0 = n0 - 10`.
Proof.
Intuition Omega.
Save.

(* Why obligation from file "mac_carthy.mlw", characters 181-187 *)
Lemma f91_po_4 : 
  (Variant1: Z)
  (n0: Z)
  (Pre2: Variant1 = (max `0` `101 - n0`))
  (Test1: `n0 > 100`)
  `n0 <= 100` /\ `n0 - 10 = 91` \/ `n0 >= 101` /\ `n0 - 10 = n0 - 10`.
Proof.
Intuition Omega.
Save.

Definition f91 := (* validation *)
  [n: Z]
    (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`) [Variant1: Z]
      (n0: Z)(_: Variant1 = (max `0` `101 - n0`))
      (sig_1 Z [result: Z](`n0 <= 100` /\ `result = 91` \/ `n0 >= 101` /\
       `result = n0 - 10`))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (n0: Z)(_: Variant2 = (max `0` `101 - n0`))
       (sig_1 Z [result: Z](`n0 <= 100` /\ `result = 91` \/ `n0 >= 101` /\
        `result = n0 - 10`));
       n0: Z; Pre2: Variant1 = (max `0` `101 - n0`)]
        let (result, Bool3) =
          let (result1, Post2) = (Z_le_gt_bool n0 `100`) in
          (exist_1 [result2: bool]
          (if result2 then `n0 <= 100` else `n0 > 100`) result1 Post2) in
        (Cases (btest
                [result:bool](if result then `n0 <= 100` else `n0 > 100`)
                result Bool3) of
        | (left Test2) =>
            let (result0, Post4) =
              let (aux_3, Post5) =
                let (result2, Post6) =
                  ((wf1 (max `0` `101 - (n0 + 11)`))
                    (f91_po_1 Variant1 n0 Pre2 Test2) `n0 + 11`
                    (refl_equal ? (max `0` `101 - (n0 + 11)`))) in
                (exist_1 [result3: Z]`n0 + 11 <= 100` /\ `result3 = 91` \/
                `n0 + 11 >= 101` /\ `result3 = n0 + 11 - 10` result2 Post6) in
              let (result0, Post7) =
                let (result2, Post8) =
                  ((wf1 (max `0` `101 - aux_3`))
                    (f91_po_2 Variant1 n0 Pre2 Test2 aux_3 Post5) aux_3
                    (refl_equal ? (max `0` `101 - aux_3`))) in
                (exist_1 [result3: Z]`aux_3 <= 100` /\ `result3 = 91` \/
                `aux_3 >= 101` /\ `result3 = aux_3 - 10` result2 Post8) in
              (exist_1 [result1: Z]`n0 <= 100` /\ `result1 = 91` \/
              `n0 >= 101` /\ `result1 = n0 - 10` result0
              (f91_po_3 Variant1 n0 Pre2 Test2 aux_3 Post5 result0 Post7)) in
            (exist_1 [result1: Z]`n0 <= 100` /\ `result1 = 91` \/
            `n0 >= 101` /\ `result1 = n0 - 10` result0 Post4)
        | (right Test1) =>
            let (result0, Post3) = (exist_1 [result0: Z]`n0 <= 100` /\
              `result0 = 91` \/ `n0 >= 101` /\ `result0 = n0 - 10` `n0 - 10`
              (f91_po_4 Variant1 n0 Pre2 Test1)) in
            (exist_1 [result1: Z]`n0 <= 100` /\ `result1 = 91` \/
            `n0 >= 101` /\ `result1 = n0 - 10` result0 Post3) end)
      (max `0` `101 - n`) n (refl_equal ? (max `0` `101 - n`))).

