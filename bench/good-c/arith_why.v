(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

(* Why obligation from file "good-c/arith.c", characters 59-166 *)
Lemma test_po_1 : 
  (k: Z)
  (j: Z)
  (result: Z)
  (Post4: result = `1`)
  (i0: Z)
  (Post1: i0 = `j + k`)
  (l0: Z)
  (Post2: l0 = `result * j`)
  (j0: Z)
  (Post3: j0 = `j + (l0 + 10 * k + i0)`)
  `i0 = j + k` /\ `j0 = 3 * j + 11 * k`.
Proof.
Intuition.
Subst result; Omega.
Save.

Definition test := (* validation *)
  [k: Z; i: Z; j: Z]
    let (result, Post4) = (exist_1 [result: Z]result = `1` `1`
      (refl_equal ? `1`)) in
    let (i0, j0, l0, result0, Post5) =
      let (i0, result0, Post1) =
        let (result0, Post1) = (exist_1 [result0: Z]result0 = `j + k` 
          `j + k` (refl_equal ? `j + k`)) in
        (exist_2 [i1: Z][result1: unit]i1 = `j + k` result0 tt Post1) in
      let (l0, result1, Post2) =
        let (result1, Post2) = (exist_1 [result1: Z]
          result1 = `result * j` `result * j` (refl_equal ? `result * j`)) in
        (exist_2 [l1: Z][result2: unit]l1 = `result * j` result1 tt Post2) in
      let (j0, result2, Post3) =
        let (result2, Post3) = (exist_1 [result2: Z]
          result2 = `j + (l0 + 10 * k + i0)` `j + (l0 + 10 * k + i0)`
          (refl_equal ? `j + (l0 + 10 * k + i0)`)) in
        (exist_2 [j1: Z][result3: unit]j1 = `j + (l0 + 10 * k + i0)` 
        result2 tt Post3) in
      (exist_4 [i1: Z][j1: Z][l1: Z][result3: unit]`i1 = j + k` /\
      `j1 = 3 * j + 11 * k` i0 j0 l0 result2
      (test_po_1 k j result Post4 i0 Post1 l0 Post2 j0 Post3)) in
    (exist_3 [i1: Z][j1: Z][result1: unit]`i1 = j + k` /\
    `j1 = 3 * j + 11 * k` i0 j0 result0 Post5).

