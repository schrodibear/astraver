
Require Why.


(* Why obligation from file "good/init.mlw", characters 41-81 *)
Lemma f_po_1 : 
  (x: Z)
  (x0: Z)
  (Post1: x0 = `1 - x`)
  `x0 = 1 - x`.
Proof.
Intuition.
Save.

Definition f := (* validation *)
  [u: unit; x: Z]
    let (x0, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `1 - x` `1 - x`
        (refl_equal ? `1 - x`)) in
      (exist_2 [x1: Z][result0: unit]x1 = `1 - x` result tt Post1) in
    (exist_2 [x1: Z][result0: unit]`x1 = 1 - x` x0 result
    (f_po_1 x x0 Post1)).

(* Why obligation from file "good/init.mlw", characters 100-143 *)
Lemma g_po_1 : 
  (x: Z)
  (x0: Z)
  (Post1: `x0 = 1 - x`)
  (x1: Z)
  (Post3: `x1 = 1 - x0`)
  `x1 = x`.
Proof.
Intuition.
Save.

Definition g := (* validation *)
  [u: unit; x: Z]
    let (x0, result, Post1) =
      let (x0, result1, Post2) = (f tt x) in
      (exist_2 [x1: Z][result2: unit]`x1 = 1 - x` x0 result1 Post2) in
    let (x1, result0, Post3) =
      let (x1, result2, Post4) = (f tt x0) in
      (exist_2 [x2: Z][result3: unit]`x2 = 1 - x0` x1 result2 Post4) in
    (exist_2 [x2: Z][result1: unit]`x2 = x` x1 result0
    (g_po_1 x x0 Post1 x1 Post3)).

