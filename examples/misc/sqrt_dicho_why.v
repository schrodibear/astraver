(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

Lemma mean1 : (x,y:Z) `x<=y` -> `x <= (x+y)/2 `.
Proof.
Intros.
Assert `(x+y)/2 >= (x+x)/2`.
Apply Z_div_ge; Omega.
Assert `(x+x)/2 = x`; Auto with *.
Replace `x+x` with `0 + x*2`; Auto with *.
Rewrite (Z_div_plus `0` x `2`); Auto with *.
Save.

Lemma mean2 : (x,y:Z) `x<y` -> `(x+y)/2 < y`.
Proof.
Intros.
Apply (!Zlt_Zmult_right2 `(x+y)/2` `y` `2`).
Auto with *.
Replace `(x+y)/2*2` with `2*((x+y)/2)`; Auto with *.
Assert `2*((x+y)/2) <= x+y`.
Apply (Z_mult_div_ge `x+y` `2`).
Auto with *.
Omega.
Save.

Hints Resolve mean1 mean2.

(* Why obligation from file "sqrt_dicho.mlw", characters 326-346 *)
Lemma sqrt_po_1 : 
  (x: Z)
  (Pre5: `x >= 0`)
  (result: Z)
  (Post7: result = `0`)
  (result0: Z)
  (Post6: result0 = `x + 1`)
  (result1: Z)
  (Post5: result1 = `0`)
  (Variant1: Z)
  (inf0: Z)
  (sup0: Z)
  (Pre4: Variant1 = `sup0 - inf0`)
  (Pre3: `inf0 * inf0 <= x` /\ `x < sup0 * sup0` /\ `inf0 < sup0`)
  (Test4: `inf0 + 1 <> sup0`)
  ~(`2` = `0`).
Proof.
Intuition.
Save.

(* Why obligation from file "sqrt_dicho.mlw", characters 375-386 *)
Lemma sqrt_po_2 : 
  (x: Z)
  (Pre5: `x >= 0`)
  (result: Z)
  (Post7: result = `0`)
  (result0: Z)
  (Post6: result0 = `x + 1`)
  (result1: Z)
  (Post5: result1 = `0`)
  (Variant1: Z)
  (inf0: Z)
  (sup0: Z)
  (Pre4: Variant1 = `sup0 - inf0`)
  (Pre3: `inf0 * inf0 <= x` /\ `x < sup0 * sup0` /\ `inf0 < sup0`)
  (Test4: `inf0 + 1 <> sup0`)
  (Pre2: ~(`2` = `0`))
  (mil1: Z)
  (Post1: mil1 = (Zdiv (`inf0 + (sup0 + 1)`) `2`))
  (Test3: `x < mil1 * mil1`)
  (sup1: Z)
  (Post2: sup1 = mil1)
  (`inf0 * inf0 <= x` /\ `x < sup1 * sup1` /\ `inf0 < sup1`) /\
  (Zwf `0` `sup1 - inf0` `sup0 - inf0`).
Proof.
Intuition.
Subst sup1; Trivial.
Subst mil1 sup1.
Replace `inf0+(sup0+1)` with `(inf0+(sup0-1))+1*2`; Try Omega.
Rewrite Z_div_plus; Try Omega.
Assert `inf0 <= (inf0+(sup0-1))/2`.
Apply mean1; Omega.
Omega.
Unfold Zwf.
Split; Try Omega.
Subst mil1 sup1. 
Replace `inf0+(sup0+1)` with `(inf0+1)+sup0`; Try Omega.
Assert `((inf0+1)+sup0)/2 < sup0`.
Apply mean2; Omega.
Omega.
Save.

(* Why obligation from file "sqrt_dicho.mlw", characters 392-403 *)
Lemma sqrt_po_3 : 
  (x: Z)
  (Pre5: `x >= 0`)
  (result: Z)
  (Post7: result = `0`)
  (result0: Z)
  (Post6: result0 = `x + 1`)
  (result1: Z)
  (Post5: result1 = `0`)
  (Variant1: Z)
  (inf0: Z)
  (sup0: Z)
  (Pre4: Variant1 = `sup0 - inf0`)
  (Pre3: `inf0 * inf0 <= x` /\ `x < sup0 * sup0` /\ `inf0 < sup0`)
  (Test4: `inf0 + 1 <> sup0`)
  (Pre2: ~(`2` = `0`))
  (mil1: Z)
  (Post1: mil1 = (Zdiv (`inf0 + (sup0 + 1)`) `2`))
  (Test2: `x >= mil1 * mil1`)
  (inf1: Z)
  (Post3: inf1 = mil1)
  (`inf1 * inf1 <= x` /\ `x < sup0 * sup0` /\ `inf1 < sup0`) /\
  (Zwf `0` `sup0 - inf1` `sup0 - inf0`).
Proof.
Intuition.
Subst mil1 inf1; Omega.
Subst mil1 inf1.
Replace `inf0+(sup0+1)` with `(inf0+1)+sup0`; Try Omega.
Assert `((inf0+1)+sup0)/2 < sup0`.
Apply mean2; Omega.
Omega.
Unfold Zwf; Split; Try Omega.
Subst inf1 mil1.
Replace `inf0+(sup0+1)` with `(inf0+1)+sup0`; Try Omega.
Assert `inf0+1 <= ((inf0+1)+sup0)/2`.
Apply mean1; Omega.
Omega.
Save.

(* Why obligation from file "sqrt_dicho.mlw", characters 235-287 *)
Lemma sqrt_po_4 : 
  (x: Z)
  (Pre5: `x >= 0`)
  (result: Z)
  (Post7: result = `0`)
  (result0: Z)
  (Post6: result0 = `x + 1`)
  (result1: Z)
  (Post5: result1 = `0`)
  `result * result <= x` /\ `x < result0 * result0` /\ `result < result0`.
Proof.
Intuition.
Subst result; Omega.
Subst result0.
Ring `(x+1)*(x+1)`.
Assert `0 <= x*x`.
Auto with *.
Omega.
Save.

(* Why obligation from file "sqrt_dicho.mlw", characters 412-416 *)
Lemma sqrt_po_5 : 
  (x: Z)
  (Pre5: `x >= 0`)
  (result: Z)
  (Post7: result = `0`)
  (result0: Z)
  (Post6: result0 = `x + 1`)
  (result1: Z)
  (Post5: result1 = `0`)
  (inf0: Z)
  (sup0: Z)
  (Post4: (`inf0 * inf0 <= x` /\ `x < sup0 * sup0` /\ `inf0 < sup0`) /\
          `inf0 + 1 = sup0`)
  `inf0 * inf0 <= x` /\ `x < (inf0 + 1) * (inf0 + 1)`.
Proof.
Intuition.
Rewrite H0; Assumption.
Save.

Definition sqrt (* validation *)
  : (x: Z)(_: `x >= 0`)
    (sig_1 Z [result: Z](`result * result <= x` /\
     `x < (result + 1) * (result + 1)`))
  := [x: Z; Pre5: `x >= 0`]
       let (result, Post10) =
         let (result, Post7) = (exist_1 [result: Z]result = `0` `0`
           (refl_equal ? `0`)) in
         let (inf0, result0, Post11) =
           let (result0, Post6) = (exist_1 [result0: Z]
             result0 = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
           let (inf0, sup0, result1, Post12) =
             let (result1, Post5) = (exist_1 [result1: Z]result1 = `0` 
               `0` (refl_equal ? `0`)) in
             let (inf0, mil0, sup0, result2, Post13) =
               let (inf0, mil0, sup0, result2, Post4) =
                 (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `
                   0`) [Variant1: Z](inf0: Z)(mil0: Z)(sup0: Z)
                   (_: Variant1 = `sup0 - inf0`)(_0: `inf0 * inf0 <= x` /\
                   `x < sup0 * sup0` /\ `inf0 < sup0`)
                   (sig_4 Z Z Z unit [inf1: Z][mil1: Z][sup1: Z]
                    [result2: unit]((`inf1 * inf1 <= x` /\
                    `x < sup1 * sup1` /\ `inf1 < sup1`) /\ `inf1 + 1 = sup1`))
                   [Variant1: Z; wf1: (Variant2: Z)
                    (Pre1: (Zwf `0` Variant2 Variant1))(inf0: Z)(mil0: Z)
                    (sup0: Z)(_: Variant2 = `sup0 - inf0`)
                    (_0: `inf0 * inf0 <= x` /\ `x < sup0 * sup0` /\
                    `inf0 < sup0`)
                    (sig_4 Z Z Z unit [inf1: Z][mil1: Z][sup1: Z]
                     [result2: unit]((`inf1 * inf1 <= x` /\
                     `x < sup1 * sup1` /\ `inf1 < sup1`) /\
                     `inf1 + 1 = sup1`));
                    inf0: Z; mil0: Z; sup0: Z;
                    Pre4: Variant1 = `sup0 - inf0`;
                    Pre3: `inf0 * inf0 <= x` /\ `x < sup0 * sup0` /\
                    `inf0 < sup0`]
                     let (result2, Bool2) =
                       let (result4, Post14) =
                         (Z_noteq_bool `inf0 + 1` sup0) in
                       (exist_1 [result5: bool]
                       (if result5 then `inf0 + 1 <> sup0`
                        else `inf0 + 1 = sup0`) result4
                       Post14) in
                     (Cases (btest
                             [result2:bool](if result2
                                            then `inf0 + 1 <> sup0`
                                            else `inf0 + 1 = sup0`)
                             result2 Bool2) of
                     | (left Test4) =>
                         let (inf1, mil1, sup1, result3, Post4) =
                           let (inf1, mil1, sup1, result3, Post8) =
                             let Pre2 =
                               (sqrt_po_1 x Pre5 result Post7 result0 Post6
                               result1 Post5 Variant1 inf0 sup0 Pre4 Pre3
                               Test4) in
                             let (mil1, result3, Post1) =
                               let (result3, Post1) = (exist_1 [result3: Z]
                                 result3 = (Zdiv (`inf0 + (sup0 + 1)`) `2`) 
                                 (Zdiv (`inf0 + (sup0 + 1)`) `2`)
                                 (refl_equal ? (Zdiv (`inf0 + (sup0 + 1)`)
                                                `2`))) in
                               (exist_2 [mil2: Z][result4: unit]
                               mil2 = (Zdiv (`inf0 + (sup0 + 1)`) `2`) 
                               result3 tt Post1) in
                             let (inf1, sup1, result4, Post8) =
                               let (result4, Bool1) =
                                 let (result6, Post15) =
                                   (Z_lt_ge_bool x `mil1 * mil1`) in
                                 (exist_1 [result7: bool]
                                 (if result7 then `x < mil1 * mil1`
                                  else `x >= mil1 * mil1`) result6
                                 Post15) in
                               (Cases (btest
                                       [result4:bool](if result4
                                                      then `x < mil1 * mil1`
                                                      else `x >= mil1 * mil1`)
                                       result4 Bool1) of
                               | (left Test3) =>
                                   let (sup1, result5, Post2) =
                                     let (result5, Post2) =
                                       (exist_1 [result5: Z]
                                       result5 = mil1 mil1
                                       (refl_equal ? mil1)) in
                                     (exist_2 [sup2: Z][result6: unit]
                                     sup2 = mil1 result5 tt Post2) in
                                   (exist_3 [inf1: Z][sup2: Z][result6: unit]
                                   (`inf1 * inf1 <= x` /\
                                   `x < sup2 * sup2` /\ `inf1 < sup2`) /\
                                   (Zwf `0` `sup2 - inf1` `sup0 - inf0`) 
                                   inf0 sup1 result5
                                   (sqrt_po_2 x Pre5 result Post7 result0
                                   Post6 result1 Post5 Variant1 inf0 sup0
                                   Pre4 Pre3 Test4 Pre2 mil1 Post1 Test3 sup1
                                   Post2))
                               | (right Test2) =>
                                   let (inf1, result5, Post3) =
                                     let (result5, Post3) =
                                       (exist_1 [result5: Z]
                                       result5 = mil1 mil1
                                       (refl_equal ? mil1)) in
                                     (exist_2 [inf2: Z][result6: unit]
                                     inf2 = mil1 result5 tt Post3) in
                                   (exist_3 [inf2: Z][sup1: Z][result6: unit]
                                   (`inf2 * inf2 <= x` /\
                                   `x < sup1 * sup1` /\ `inf2 < sup1`) /\
                                   (Zwf `0` `sup1 - inf2` `sup0 - inf0`) 
                                   inf1 sup0 result5
                                   (sqrt_po_3 x Pre5 result Post7 result0
                                   Post6 result1 Post5 Variant1 inf0 sup0
                                   Pre4 Pre3 Test4 Pre2 mil1 Post1 Test2 inf1
                                   Post3)) end) in
                             (exist_4 [inf2: Z][mil2: Z][sup2: Z]
                             [result5: unit](`inf2 * inf2 <= x` /\
                             `x < sup2 * sup2` /\ `inf2 < sup2`) /\
                             (Zwf `0` `sup2 - inf2` `sup0 - inf0`) inf1 
                             mil1 sup1 result4 Post8) in
                           ((wf1 `sup1 - inf1`) (loop_variant_1 Pre4 Post8)
                             inf1 mil1 sup1 (refl_equal ? `sup1 - inf1`)
                             (proj1 ? ? Post8)) in
                         (exist_4 [inf2: Z][mil2: Z][sup2: Z][result4: unit]
                         (`inf2 * inf2 <= x` /\ `x < sup2 * sup2` /\
                         `inf2 < sup2`) /\ `inf2 + 1 = sup2` inf1 mil1 
                         sup1 result3 Post4)
                     | (right Test1) =>
                         let (inf1, mil1, sup1, result3, Post4) =
                           (exist_4 [inf1: Z][mil1: Z][sup1: Z]
                           [result3: unit](`inf1 * inf1 <= x` /\
                           `x < sup1 * sup1` /\ `inf1 < sup1`) /\
                           `inf1 + 1 = sup1` inf0 mil0 sup0 tt
                           (conj ? ? Pre3 Test1)) in
                         (exist_4 [inf2: Z][mil2: Z][sup2: Z][result4: unit]
                         (`inf2 * inf2 <= x` /\ `x < sup2 * sup2` /\
                         `inf2 < sup2`) /\ `inf2 + 1 = sup2` inf1 mil1 
                         sup1 result3 Post4) end) `result0 - result` 
                   result result1 result0 (refl_equal ? `result0 - result`)
                   (sqrt_po_4 x Pre5 result Post7 result0 Post6 result1
                   Post5)) in
               let (result3, Post16) = (exist_1 [result3: Z]
                 `result3 * result3 <= x` /\
                 `x < (result3 + 1) * (result3 + 1)` inf0
                 (sqrt_po_5 x Pre5 result Post7 result0 Post6 result1 Post5
                 inf0 sup0 Post4)) in
               (exist_4 [inf1: Z][mil1: Z][sup1: Z][result4: Z]
               `result4 * result4 <= x` /\
               `x < (result4 + 1) * (result4 + 1)` inf0 mil0 sup0 result3
               Post16) in
             (exist_3 [inf1: Z][sup1: Z][result3: Z]
             `result3 * result3 <= x` /\
             `x < (result3 + 1) * (result3 + 1)` inf0 sup0 result2 Post13) in
           (exist_2 [inf1: Z][result2: Z]`result2 * result2 <= x` /\
           `x < (result2 + 1) * (result2 + 1)` inf0 result1 Post12) in
         (exist_1 [result1: Z]`result1 * result1 <= x` /\
         `x < (result1 + 1) * (result1 + 1)` result0 Post11) in
       (exist_1 [result0: Z]`result0 * result0 <= x` /\
       `x < (result0 + 1) * (result0 + 1)` result Post10).

