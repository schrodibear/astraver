(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

(* Why obligation from file "good-c/rec.c", characters 115-123 *)
Lemma f_po_1 : 
  (x: Z)
  (Pre8: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre7: Variant1 = x0)
  (Pre6: `x0 >= 0`)
  (Test1: `x0 <> 0`)
  `x0 - 1 >= 0`.
Proof.
Intuition.
Save.

(* Why obligation from file "good-c/rec.c", characters 46-144 *)
Lemma f_po_2 : 
  (x: Z)
  (Pre8: `x >= 0`)
  (Variant1: Z)
  (x0: Z)
  (Pre7: Variant1 = x0)
  (Pre6: `x0 >= 0`)
  (Test1: `x0 <> 0`)
  (Pre5: `x0 - 1 >= 0`)
  (Pre3: `x0 - 1 >= 0`)
  (Pre4: `x0 - 1 >= 0`)
  (Zwf `0` `x0 - 1` Variant1).
Proof.
Intuition.
Unfold Zwf; Omega.
Save.

Definition f (* validation *)
  : (x: Z)(_: `x >= 0`)(sig_1 Z [result: Z](`result = 0`))
  := [x: Z; Pre8: `x >= 0`]
       (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
         [Variant1: Z](x0: Z)(_: Variant1 = x0)(_0: `x0 >= 0`)
         (sig_1 Z [result: Z](`result = 0`))
         [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
          (x0: Z)(_: Variant2 = x0)(_0: `x0 >= 0`)
          (sig_1 Z [result: Z](`result = 0`)); x0: Z; Pre7: Variant1 = x0;
          Pre6: `x0 >= 0`]
           let (result, Bool3) =
             let (result1, Post2) = (Z_eq_bool x0 `0`) in
             (exist_1 [result2: bool]
             (if result2 then `x0 = 0` else `x0 <> 0`) result1 Post2) in
           (Cases (btest
                   [result:bool](if result then `x0 = 0` else `x0 <> 0`)
                   result Bool3) of
           | (left Test2) =>
               let (result0, Post5) = (exist_1 [result0: Z]`result0 = 0` 
                 `0` (refl_equal ? `0`)) in
               (exist_1 [result1: Z]`result1 = 0` result0 Post5)
           | (right Test1) =>
               let Pre5 = (f_po_1 x Pre8 Variant1 x0 Pre7 Pre6 Test1) in
               let (result0, Post3) =
                 let Pre3 = Pre5 in
                 let Pre4 = Pre3 in
                 let (result2, Post4) =
                   ((wf1 `x0 - 1`)
                     (f_po_2 x Pre8 Variant1 x0 Pre7 Pre6 Test1 Pre5 Pre3
                     Pre4) `x0 - 1` (refl_equal ? `x0 - 1`) Pre4) in
                 (exist_1 [result3: Z]`result3 = 0` result2 Post4) in
               (exist_1 [result1: Z]`result1 = 0` result0 Post3) end) 
         x x (refl_equal ? x) Pre8).

