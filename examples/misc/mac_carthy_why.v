(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

Lemma f91_po_1 : 
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with *.
Save.

Definition max : Z->Z->Z := 
  [x,y] Cases (Z_le_gt_dec x y) of (left _) => y | (right _) => x end.

Lemma f91_po_2 : 
  (Variant1: Z)
  (n: Z)
  (Pre2: Variant1 = (max `0` `101 - n`))
  (Test2: `n <= 100`)
  (Zwf `0` (max `0` `101 - (n + 11)`) Variant1).
Proof.
Intros Variant1 n. Unfold Zwf max.
Case (Z_le_gt_dec `0` `101-n`); Intros Pre2 Test2;
Case (Z_le_gt_dec `0` `101-(n+11)`); Intuition; Omega.
Save.

Lemma f91_po_3 : 
  (Variant1: Z)
  (n: Z)
  (Pre2: Variant1 = (max `0` `101 - n`))
  (Test2: `n <= 100`)
  (aux_2: Z)
  (Post5: `n + 11 <= 100` /\ aux_2 = `91` \/ `n + 11 >= 101` /\
          aux_2 = `n + 11 - 10`)
  (Zwf `0` (max `0` `101 - aux_2`) Variant1).
Proof.
Intros Variant1 n. Unfold Zwf max.
Case (Z_le_gt_dec `0` `101-n`); Intros H Pre2 Test2 aux_2 Post5;
Case (Z_le_gt_dec `0` `101-aux_2`); Intuition Omega.
Save.

Lemma f91_po_4 : 
  (Variant1: Z)
  (n: Z)
  (Pre2: Variant1 = (max `0` `101 - n`))
  (Test2: `n <= 100`)
  (aux_2: Z)
  (Post5: `n + 11 <= 100` /\ aux_2 = `91` \/ `n + 11 >= 101` /\
          aux_2 = `n + 11 - 10`)
  (result0: Z)
  (Post7: `aux_2 <= 100` /\ result0 = `91` \/ `aux_2 >= 101` /\
          result0 = `aux_2 - 10`)
  `n <= 100` /\ result0 = `91` \/ `n >= 101` /\ result0 = `n - 10`.
Proof.
Intuition Omega.
Save.

Lemma f91_po_5 : 
  (Variant1: Z)
  (n: Z)
  (Pre2: Variant1 = (max `0` `101 - n`))
  (Test1: `n > 100`)
  `n <= 100` /\ `n - 10` = `91` \/ `n >= 101` /\ `n - 10` = `n - 10`.
Proof.
Intuition Omega.
Save.



Definition f91 := (* validation *)
  [n: Z]
    (well_founded_induction Z (Zwf ZERO) f91_po_1 [Variant1: Z](n: Z)
      (_: Variant1 = (max `0` `101 - n`))
      (sig_1 Z [result:Z](`n <= 100` /\ result = `91` \/ `n >= 101` /\
       result = `n - 10`))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (n: Z)(_: Variant2 = (max `0` `101 - n`))
       (sig_1 Z [result:Z](`n <= 100` /\ result = `91` \/ `n >= 101` /\
        result = `n - 10`));
       n: Z; Pre2: Variant1 = (max `0` `101 - n`)]
        let (result, Bool1) =
          let (result1, Post2) = (Z_le_gt_bool n `100`) in
          (exist_1 [result2: bool]
          (if result2 then `n <= 100` else `n > 100`) result1 Post2) in
        (Cases (btest [result:bool](if result then `n <= 100` else `n > 100`)
                result Bool1) of
        | (left Test2) =>
            let (result0, Post4) =
              let (aux_2, Post5) =
                let (result2, Post6) =
                  ((wf1 (max `0` `101 - (n + 11)`))
                    (f91_po_2 Variant1 n Pre2 Test2) `n + 11`
                    (refl_equal ? (max `0` `101 - (n + 11)`))) in
                (exist_1 [result3: Z]`n + 11 <= 100` /\ result3 = `91` \/
                `n + 11 >= 101` /\ result3 = `n + 11 - 10` result2 Post6) in
              let (result0, Post7) =
                let (result2, Post8) =
                  ((wf1 (max `0` `101 - aux_2`))
                    (f91_po_3 Variant1 n Pre2 Test2 aux_2 Post5) aux_2
                    (refl_equal ? (max `0` `101 - aux_2`))) in
                (exist_1 [result3: Z]`aux_2 <= 100` /\ result3 = `91` \/
                `aux_2 >= 101` /\ result3 = `aux_2 - 10` result2 Post8) in
              (exist_1 [result1: Z]`n <= 100` /\ result1 = `91` \/
              `n >= 101` /\ result1 = `n - 10` result0
              (f91_po_4 Variant1 n Pre2 Test2 aux_2 Post5 result0 Post7)) in
            (exist_1 [result1: Z]`n <= 100` /\ result1 = `91` \/
            `n >= 101` /\ result1 = `n - 10` result0 Post4)
        | (right Test1) =>
            let (result0, Post3) = (exist_1 [result0: Z]`n <= 100` /\
              result0 = `91` \/ `n >= 101` /\ result0 = `n - 10` `n - 10`
              (f91_po_5 Variant1 n Pre2 Test1)) in
            (exist_1 [result1: Z]`n <= 100` /\ result1 = `91` \/
            `n >= 101` /\ result1 = `n - 10` result0 Post3) end)
      (max `0` `101 - n`) n (refl_equal ? (max `0` `101 - n`))).

