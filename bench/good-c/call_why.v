(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.


(* Why obligation from file "good-c/call.c", characters 113-116 *)
Lemma f_po_1 : 
  (y: Z)
  (ddd: Z)
  (z: Z)
  (Pre1: `y = ddd`)
  (result: Z)
  (Post3: result = z)
  (c_aux_1: Z)
  (Post2: c_aux_1 = result)
  (u0: Z)
  (Post1: u0 = `result + 1`)
  `c_aux_1 = z`.
Proof.
Intuition.
Save.

Definition f := (* validation *)
  [y: Z; ddd: Z; z: Z; Pre1: `y = ddd`]
    let (result, Post3) = (exist_1 [result: Z]result = z z
      (refl_equal ? z)) in
    let (u0, result0, Post4) =
      let (c_aux_1, Post2) = (exist_1 [result0: Z]result0 = result result
        (refl_equal ? result)) in
      let (u0, result0, Post5) =
        let (u0, result0, Post1) =
          let (result0, Post1) = (exist_1 [result0: Z]
            result0 = `result + 1` `result + 1`
            (refl_equal ? `result + 1`)) in
          (exist_2 [u1: Z][result1: unit]u1 = `result + 1` result0 tt Post1) in
        let (result1, Post6) = (exist_1 [result1: Z]`result1 = z` c_aux_1
          (f_po_1 y ddd z Pre1 result Post3 c_aux_1 Post2 u0 Post1)) in
        (exist_2 [u1: Z][result2: Z]`result2 = z` u0 result1 Post6) in
      (exist_2 [u1: Z][result1: Z]`result1 = z` u0 result0 Post5) in
    (exist_1 [result1: Z]`result1 = z` result0 Post4).

(* Why obligation from file "good-c/call.c", characters 174-177 *)
Lemma main_po_1 : 
  (x0: Z)
  (Post1: x0 = `0`)
  (x1: Z)
  (Post2: x1 = `x0 + 1`)
  ((result:Z) (`result = 2` -> `result = 2`)) /\ `1 = x1`.
Proof.
Intuition.
Save.

(* Why obligation from file "good-c/call.c", characters 170-180 *)
Lemma main_po_2 : 
  (x0: Z)
  (Post1: x0 = `0`)
  (c_aux_2: Z)
  (Post5: ((result:Z) (`result = 2` -> `result = 2`)) /\ `1 = c_aux_2`)
  `1 = c_aux_2`.
Proof.
Intuition.
Save.

Definition main := (* validation *)
  [_: unit; x: Z]
    let (x0, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `0` `0`
        (refl_equal ? `0`)) in
      (exist_2 [x1: Z][result0: unit]x1 = `0` result tt Post1) in
    let (x1, result0, Post3) =
      let (x1, result0, Post4) =
        let (x1, c_aux_2, Post5) =
          let (x1, result0, Post2) =
            let (result0, Post2) = (exist_1 [result0: Z]
              result0 = `x0 + 1` `x0 + 1` (refl_equal ? `x0 + 1`)) in
            (exist_2 [x2: Z][result1: unit]x2 = `x0 + 1` result0 tt Post2) in
          let (result1, Post6) = (exist_1 [result1: Z]
            ((result:Z) (`result = 2` -> `result = 2`)) /\ `1 = result1` 
            x1 (main_po_1 x0 Post1 x1 Post2)) in
          (exist_2 [x2: Z][result2: Z]
          ((result:Z) (`result = 2` -> `result = 2`)) /\ `1 = result2` 
          x1 result1 Post6) in
        let Pre3 = (main_po_2 x0 Post1 c_aux_2 Post5) in
        let (result0, Post7) =
          let Pre1 = Pre3 in
          let Pre2 = Pre1 in
          let (result2, Post8) = (f `1` c_aux_2 `2` Pre1) in
          (exist_1 [result3: Z]`result3 = 2` result2 Post8) in
        (exist_2 [x2: Z][result1: Z]`result1 = 2` x1 result0 Post7) in
      (exist_2 [x3: Z][result1: unit]`x3 = 2` result0 tt Post4) in
    (exist_2 [x2: Z][result1: unit]`x2 = 2` x1 result0 Post3).

