(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require WhyFloat.

Definition g := (* validation *)
  [x: Z]
    let (result, Post1) = (exist_1 [result: Z]`result = 0` `0`
      (refl_equal ? `0`)) in
    (exist_2 [x1: Z][result0: unit]`x1 = 0` result tt Post1).

Definition g2 := (* validation *)
  [_: unit; r: Z]
    let (r0, result, Post1) =
      let (r0, result0, Post2) = (g r) in
      (exist_2 [r1: Z][result1: unit]`r1 = 0` r0 result0 Post2) in
    let (result0, Post3) = (exist_1 [result0: Z]`result0 = 0` r0 Post1) in
    (exist_2 [r1: Z][result1: Z]`result1 = 0` r0 result0 Post3).

Definition g3 := (* validation *)
  [_: unit]
    let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
      (refl_equal ? `1`)) in
    let (i0, result0, Post2) =
      let (i0, result0, Post3) =
        let (i0, result1, Post4) = (g result) in
        (exist_2 [i1: Z][result2: unit]`i1 = 0` i0 result1 Post4) in
      let (result1, Post5) = (exist_1 [result1: Z]`result1 = 0` i0 Post3) in
      (exist_2 [i1: Z][result2: Z]`result2 = 0` i0 result1 Post5) in
    (exist_1 [result1: Z]`result1 = 0` result0 Post2).

(* Why obligation from file "good-c/passing.c", characters 212-267 *)
Lemma f_po_1 : 
  (x: (array Z))
  (Pre2: `(array_length x) = 1`)
  `0 <= 0` /\ `0 < (array_length x)`.
Proof.
Intuition.
Save.

(* Why obligation from file "good-c/passing.c", characters 212-267 *)
Lemma f_po_2 : 
  (x: (array Z))
  (Pre2: `(array_length x) = 1`)
  (Pre1: `0 <= 0` /\ `0 < (array_length x)`)
  `(access (store x 0 1) 0) = 1`.
Proof.
Intuition.
Save.

Definition f := (* validation *)
  [x: (array Z); Pre2: `(array_length x) = 1`]
    let Pre1 = (f_po_1 x Pre2) in
    (exist_2 [x1: (array Z)][result1: unit]
    `(access x1 0) = 1` (store x `0` `1`) tt (f_po_2 x Pre2 Pre1)).

Definition main := (* validation *)
  [_: unit; t: (array Z); Pre2: `(array_length t) = 1`]
    let Pre1 = Pre2 in
    let (t0, result0, Post1) = (f t Pre1) in
    (exist_2 [t1: (array Z)][result1: unit]`(access t1 0) = 1` t0 result0
    Post1).

