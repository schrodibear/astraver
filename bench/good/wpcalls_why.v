(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

(*Why*) Parameter f :
  (_: unit)(x: Z)(sig_2 Z unit [x0: Z][result: unit](`x0 = 1 - x`)).

(* Why obligation from file "good/wpcalls.mlw", characters 130-134 *)
Lemma p_po_1 : 
  (x: Z)
  (t: unit)
  (Post1: t = tt)
  ((x0:Z) (`x0 = 1 - x` -> ((x1:Z) (`x1 = 1 - x0` -> `x1 = x`)))).
Proof.
Intuition.
Save.

Definition p (* validation *)
  : (u: unit)(x: Z)(sig_2 Z unit [x0: Z][result: unit](True))
  := [u: unit; x: Z]
       let (result, Post2) =
         let (t, Post1) = (exist_1 [result: unit]result = tt tt
           (refl_equal ? tt)) in
         let (result, Post3) = (exist_1 [result: unit]
           ((x0:Z) (`x0 = 1 - x` -> ((x1:Z) (`x1 = 1 - x0` -> `x1 = x`)))) 
           tt (p_po_1 x t Post1)) in
         (exist_1 [result0: unit]
         ((x0:Z) (`x0 = 1 - x` -> ((x1:Z) (`x1 = 1 - x0` -> `x1 = x`)))) 
         result Post3) in
       let (x0, result0, Post4) =
         let (x0, result2, Post5) = (f tt x) in
         (exist_2 [x1: Z][result3: unit]`x1 = 1 - x` x0 result2 Post5) in
       let (x1, result1, Post6) =
         let (x1, result3, Post7) = (f tt x0) in
         (exist_2 [x2: Z][result4: unit]`x2 = 1 - x0` x1 result3 Post7) in
       let Pre1 =
         let HW_1 = (Post2 x0 Post4) in
         let HW_2 = (HW_1 x1 Post6) in
         HW_2 in
       let (result2, Post8) = (exist_1 [result2: unit]True tt I) in
       (exist_2 [x2: Z][result3: unit]True x1 result2 I).

