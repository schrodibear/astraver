(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

(* Why obligation from file "good-c/sum1.c", characters 74-165 *)
Lemma main_po_1 : 
  (x: Z)
  (Pre4: `x = 0`)
  (result: Z)
  (Post5: result = `0`)
  (i0: Z)
  (Post1: i0 = `0`)
  (Variant1: Z)
  (i1: Z)
  (x0: Z)
  (Pre3: Variant1 = `10 - i1`)
  (Pre2: `x0 = i1` /\ `i1 <= 10`)
  (Test2: `i1 < 10`)
  (x1: Z)
  (Post2: x1 = `x0 + 1`)
  (i2: Z)
  (Post3: i2 = `i1 + 1`)
  (`x1 = i2` /\ `i2 <= 10`) /\ (Zwf `0` `10 - i2` `10 - i1`).
Proof.
Intuition.
Unfold Zwf; Omega.
Save.

(* Why obligation from file "good-c/sum1.c", characters 118-135 *)
Lemma main_po_2 : 
  (x: Z)
  (Pre4: `x = 0`)
  (result: Z)
  (Post5: result = `0`)
  (i0: Z)
  (Post1: i0 = `0`)
  `x = i0` /\ `i0 <= 10`.
Proof.
Intuition.
Save.

(* Why obligation from file "good-c/sum1.c", characters 74-165 *)
Lemma main_po_3 : 
  (x: Z)
  (Pre4: `x = 0`)
  (result: Z)
  (Post5: result = `0`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (x0: Z)
  (Post4: (`x0 = i1` /\ `i1 <= 10`) /\ `i1 >= 10`)
  `x0 = 10`.
Proof.
Intuition.
Save.



Definition main (* validation *)
  : (_: unit)(x: Z)(_: `x = 0`)
    (sig_2 Z unit [x0: Z][result: unit](`x0 = 10`))
  := [_: unit; x: Z; Pre4: `x = 0`]
       let (result, Post5) = (exist_1 [result: Z]result = `0` `0`
         (refl_equal ? `0`)) in
       let (i0, x0, result0, Post7) =
         let (i0, result0, Post1) =
           let (result0, Post1) = (exist_1 [result0: Z]result0 = `0` 
             `0` (refl_equal ? `0`)) in
           (exist_2 [i1: Z][result1: unit]i1 = `0` result0 tt Post1) in
         let (i1, x0, result1, Post4) =
           (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
             [Variant1: Z](i1: Z)(x0: Z)(_0: Variant1 = `10 - i1`)
             (_1: `x0 = i1` /\ `i1 <= 10`)
             (sig_3 Z Z unit [i2: Z][x1: Z][result1: unit]((`x1 = i2` /\
              `i2 <= 10`) /\ `i2 >= 10`))
             [Variant1: Z; wf1: (Variant2: Z)
              (Pre1: (Zwf `0` Variant2 Variant1))(i1: Z)(x0: Z)
              (_0: Variant2 = `10 - i1`)(_1: `x0 = i1` /\ `i1 <= 10`)
              (sig_3 Z Z unit [i2: Z][x1: Z][result1: unit]((`x1 = i2` /\
               `i2 <= 10`) /\ `i2 >= 10`));
              i1: Z; x0: Z; Pre3: Variant1 = `10 - i1`; Pre2: `x0 = i1` /\
              `i1 <= 10`]
               let (result1, Bool1) =
                 let (result3, Post8) = (Z_lt_ge_bool i1 `10`) in
                 (exist_1 [result4: bool]
                 (if result4 then `i1 < 10` else `i1 >= 10`) result3 Post8) in
               (Cases (btest
                       [result1:bool](if result1 then `i1 < 10`
                                      else `i1 >= 10`)
                       result1 Bool1) of
               | (left Test2) =>
                   let (i2, x1, result2, Post4) =
                     let (i2, x1, result2, Post6) =
                       let (x1, result2, Post2) =
                         let (result2, Post2) = (exist_1 [result2: Z]
                           result2 = `x0 + 1` `x0 + 1`
                           (refl_equal ? `x0 + 1`)) in
                         (exist_2 [x2: Z][result3: unit]x2 = `x0 + 1` 
                         result2 tt Post2) in
                       let (i2, result3, Post3) =
                         let (result3, Post3) = (exist_1 [result3: Z]
                           result3 = `i1 + 1` `i1 + 1`
                           (refl_equal ? `i1 + 1`)) in
                         (exist_2 [i3: Z][result4: unit]i3 = `i1 + 1` 
                         result3 tt Post3) in
                       (exist_3 [i3: Z][x2: Z][result4: unit](`x2 = i3` /\
                       `i3 <= 10`) /\ (Zwf `0` `10 - i3` `10 - i1`) i2 
                       x1 result3
                       (main_po_1 x Pre4 result Post5 i0 Post1 Variant1 i1 x0
                       Pre3 Pre2 Test2 x1 Post2 i2 Post3)) in
                     ((wf1 `10 - i2`) (loop_variant_1 Pre3 Post6) i2 
                       x1 (refl_equal ? `10 - i2`) (proj1 ? ? Post6)) in
                   (exist_3 [i3: Z][x2: Z][result3: unit](`x2 = i3` /\
                   `i3 <= 10`) /\ `i3 >= 10` i2 x1 result2 Post4)
               | (right Test1) =>
                   let (i2, x1, result2, Post4) = (exist_3 [i2: Z][x1: Z]
                     [result2: unit](`x1 = i2` /\ `i2 <= 10`) /\
                     `i2 >= 10` i1 x0 tt (conj ? ? Pre2 Test1)) in
                   (exist_3 [i3: Z][x2: Z][result3: unit](`x2 = i3` /\
                   `i3 <= 10`) /\ `i3 >= 10` i2 x1 result2 Post4) end)
             `10 - i0` i0 x (refl_equal ? `10 - i0`)
             (main_po_2 x Pre4 result Post5 i0 Post1)) in
         (exist_3 [i2: Z][x1: Z][result2: unit]`x1 = 10` i1 x0 result1
         (main_po_3 x Pre4 result Post5 i0 Post1 i1 x0 Post4)) in
       (exist_2 [x1: Z][result1: unit]`x1 = 10` x0 result0 Post7).

