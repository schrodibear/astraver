Require Why.
Require Omega.

(* Why obligation from file "swap0.mlw", characters 149-174 *)
Lemma swap1_po_1 : 
  (x: Z)
  (y: Z)
  (t: Z)
  (Post3: t = x)
  (x0: Z)
  (Post1: x0 = y)
  (y0: Z)
  (Post2: y0 = t)
  `x0 = y` /\ `y0 = x`.
Proof.
Intuition.
Save.

Definition swap1 (* validation *)
  : (x: Z)(y: Z)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`x0 = y` /\ `y0 = x`))
  := [x: Z; y: Z]
       let (t, Post3) = (exist_1 [result: Z]result = x x (refl_equal ? x)) in
       let (x0, y0, result, Post4) =
         let (x0, result, Post1) =
           let (result, Post1) = (exist_1 [result: Z]result = y y
             (refl_equal ? y)) in
           (exist_2 [x1: Z][result0: unit]x1 = y result tt Post1) in
         let (y0, result0, Post2) =
           let (result0, Post2) = (exist_1 [result0: Z]result0 = t t
             (refl_equal ? t)) in
           (exist_2 [y1: Z][result1: unit]y1 = t result0 tt Post2) in
         (exist_3 [x1: Z][y1: Z][result1: unit]`x1 = y` /\ `y1 = x` x0 
         y0 result0 (swap1_po_1 x y t Post3 x0 Post1 y0 Post2)) in
       (exist_3 [x1: Z][y1: Z][result0: unit]`x1 = y` /\ `y1 = x` x0 
       y0 result Post4).

(* Why obligation from file "swap0.mlw", characters 316-358 *)
Lemma swap2_po_1 : 
  (x: Z)
  (y: Z)
  (t: Z)
  (Post3: t = x)
  (x0: Z)
  (Post1: x0 = y)
  (y0: Z)
  (Post2: y0 = t)
  `x0 = y` /\ `y0 = x`.
Proof.
Intuition.
Save.

Definition swap2 (* validation *)
  : (x: Z)(y: Z)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`x0 = y` /\ `y0 = x`))
  := [x: Z; y: Z]
       let (x0, y0, result, Post4) =
         let (t, Post3) = (exist_1 [result: Z]result = x x
           (refl_equal ? x)) in
         let (x0, y0, result, Post5) =
           let (x0, result, Post1) =
             let (result, Post1) = (exist_1 [result: Z]result = y y
               (refl_equal ? y)) in
             (exist_2 [x1: Z][result0: unit]x1 = y result tt Post1) in
           let (y0, result0, Post2) =
             let (result0, Post2) = (exist_1 [result0: Z]result0 = t 
               t (refl_equal ? t)) in
             (exist_2 [y1: Z][result1: unit]y1 = t result0 tt Post2) in
           (exist_3 [x1: Z][y1: Z][result1: unit]`x1 = y` /\ `y1 = x` 
           x0 y0 result0 (swap2_po_1 x y t Post3 x0 Post1 y0 Post2)) in
         (exist_3 [x1: Z][y1: Z][result0: unit]`x1 = y` /\ `y1 = x` x0 
         y0 result Post5) in
       (exist_3 [x1: Z][y1: Z][result0: unit]`x1 = y` /\ `y1 = x` x0 
       y0 result Post4).

(* Why obligation from file "swap0.mlw", characters 509-534 *)
Lemma swap3_po_1 : 
  (a: Z)
  (b: Z)
  (t: Z)
  (Post3: t = a)
  (a0: Z)
  (Post1: a0 = b)
  (b0: Z)
  (Post2: b0 = t)
  `a0 = b` /\ `b0 = a`.
Proof.
Intuition.
Save.

Definition swap3 (* validation *)
  : (a: Z)(b: Z)
    (sig_3 Z Z unit [a0: Z][b0: Z][result: unit](`a0 = b` /\ `b0 = a`))
  := [a: Z; b: Z]
       let (t, Post3) = (exist_1 [result: Z]result = a a (refl_equal ? a)) in
       let (a0, b0, result, Post4) =
         let (a0, result, Post1) =
           let (result, Post1) = (exist_1 [result: Z]result = b b
             (refl_equal ? b)) in
           (exist_2 [a1: Z][result0: unit]a1 = b result tt Post1) in
         let (b0, result0, Post2) =
           let (result0, Post2) = (exist_1 [result0: Z]result0 = t t
             (refl_equal ? t)) in
           (exist_2 [b1: Z][result1: unit]b1 = t result0 tt Post2) in
         (exist_3 [a1: Z][b1: Z][result1: unit]`a1 = b` /\ `b1 = a` a0 
         b0 result0 (swap3_po_1 a b t Post3 a0 Post1 b0 Post2)) in
       (exist_3 [a1: Z][b1: Z][result0: unit]`a1 = b` /\ `b1 = a` a0 
       b0 result Post4).

(* Why obligation from file "swap0.mlw", characters 654-678 *)
Lemma test_swap3_po_1 : 
  (result: Z)
  (Post2: result = `1`)
  (result0: Z)
  (Post1: result0 = `2`)
  (c0: Z)
  (d0: Z)
  (Post4: `c0 = result0` /\ `d0 = result`)
  `d0 = 1`.
Proof. (* test_swap3_po_1 *)
Intuition.
Save.

Definition test_swap3 (* validation *)
  : unit
  := let (result, Post2) = (exist_1 [result: Z]result = `1` `1`
       (refl_equal ? `1`)) in
     let (c0, result0) =
       let (result0, Post1) = (exist_1 [result0: Z]result0 = `2` `2`
         (refl_equal ? `2`)) in
       let (c0, d0, result1, Post3) =
         let (c0, d0, result2, Post4) = (swap3 result result0) in
         (exist_3 [c1: Z][d1: Z][result3: unit]`d1 = 1` c0 d0 result2
         (test_swap3_po_1 result Post2 result0 Post1 c0 d0 Post4)) in
       (Build_tuple_2 c0 result1) in
     result0.

Definition call_swap3_x_y (* validation *)
  : (x: Z)(y: Z)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`x0 = y` /\ `y0 = x`))
  := [x: Z; y: Z]
       let (x0, y0, result0, Post1) = (swap3 x y) in
       (exist_3 [x1: Z][y1: Z][result1: unit]`x1 = y` /\ `y1 = x` x0 
       y0 result0 Post1).

(* Why obligation from file "swap0.mlw", characters 790-826 *)
Lemma call_swap3_y_x_po_1 : 
  (x: Z)
  (y: Z)
  (y0: Z)
  (x0: Z)
  (Post1: `y0 = x` /\ `x0 = y`)
  `x0 = y` /\ `y0 = x`.
Proof. (* call_swap3_y_x_po_1 *)
Intuition.
Save.

Definition call_swap3_y_x (* validation *)
  : (x: Z)(y: Z)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`x0 = y` /\ `y0 = x`))
  := [x: Z; y: Z]
       let (y0, x0, result0, Post1) = (swap3 y x) in
       (exist_3 [x1: Z][y1: Z][result1: unit]`x1 = y` /\ `y1 = x` x0 
       y0 result0 (call_swap3_y_x_po_1 x y y0 x0 Post1)).

(* Why obligation from file "swap0.mlw", characters 945-1014 *)
Lemma swap4_po_1 : 
  (a: Z)
  (b: Z)
  (tmp0: Z)
  (Post1: tmp0 = a)
  (a0: Z)
  (Post2: a0 = b)
  (b0: Z)
  (Post3: b0 = tmp0)
  `a0 = b` /\ `b0 = a`.
Proof.
Intuition.
Save.

Definition swap4 (* validation *)
  : (a: Z)(b: Z)(tmp: Z)
    (sig_4 Z Z Z unit [a0: Z][b0: Z][tmp0: Z][result: unit](`a0 = b` /\
     `b0 = a`))
  := [a: Z; b: Z; tmp: Z]
       let (tmp0, result, Post1) =
         let (result, Post1) = (exist_1 [result: Z]result = a a
           (refl_equal ? a)) in
         (exist_2 [tmp1: Z][result0: unit]tmp1 = a result tt Post1) in
       let (a0, result0, Post2) =
         let (result0, Post2) = (exist_1 [result0: Z]result0 = b b
           (refl_equal ? b)) in
         (exist_2 [a1: Z][result1: unit]a1 = b result0 tt Post2) in
       let (b0, result1, Post3) =
         let (result1, Post3) = (exist_1 [result1: Z]result1 = tmp0 tmp0
           (refl_equal ? tmp0)) in
         (exist_2 [b1: Z][result2: unit]b1 = tmp0 result1 tt Post3) in
       (exist_4 [a1: Z][b1: Z][tmp1: Z][result2: unit]`a1 = b` /\ `b1 = a` 
       a0 b0 tmp0 result1 (swap4_po_1 a b tmp0 Post1 a0 Post2 b0 Post3)).

(* Why obligation from file "swap0.mlw", characters 1109-1133 *)
Lemma test_swap4_po_1 : 
  (result: Z)
  (Post2: result = `1`)
  (result0: Z)
  (Post1: result0 = `2`)
  (c0: Z)
  (d0: Z)
  (Post4: `c0 = result0` /\ `d0 = result`)
  `d0 = 1`.
Proof. (* test_swap4_po_1 *)
Intuition.
Save.

Definition test_swap4 (* validation *)
  : (tmp: Z)(tuple_2 Z unit)
  := [tmp: Z]
       let (result, Post2) = (exist_1 [result: Z]result = `1` `1`
         (refl_equal ? `1`)) in
       let (c0, tmp0, result0) =
         let (result0, Post1) = (exist_1 [result0: Z]result0 = `2` `2`
           (refl_equal ? `2`)) in
         let (c0, d0, tmp0, result1, Post3) =
           let (c0, d0, tmp0, result2, Post4) = (swap4 result result0 tmp) in
           (exist_4 [c1: Z][d1: Z][tmp1: Z][result3: unit]`d1 = 1` c0 
           d0 tmp0 result2
           (test_swap4_po_1 result Post2 result0 Post1 c0 d0 Post4)) in
         (Build_tuple_3 c0 tmp0 result1) in
       (Build_tuple_2 tmp0 result0).

(* Why obligation from file "swap0.mlw", characters 1187-1218 *)
Lemma call_swap4_x_y_po_1 : 
  (x: Z)
  (y: Z)
  (Pre1: `x = 3`)
  (x0: Z)
  (y0: Z)
  (Post1: `x0 = y` /\ `y0 = x`)
  `y0 = 3`.
Proof.
Intuition.
Save.

Definition call_swap4_x_y (* validation *)
  : (tmp: Z)(x: Z)(y: Z)(_: `x = 3`)
    (sig_4 Z Z Z unit [tmp0: Z][x0: Z][y0: Z][result: unit](`y0 = 3`))
  := [tmp: Z; x: Z; y: Z; Pre1: `x = 3`]
       let (x0, y0, tmp0, result0, Post1) = (swap4 x y tmp) in
       (exist_4 [tmp1: Z][x1: Z][y1: Z][result1: unit]`y1 = 3` tmp0 x0 
       y0 result0 (call_swap4_x_y_po_1 x y Pre1 x0 y0 Post1)).

(* Why obligation from file "swap0.mlw", characters 1240-1271 *)
Lemma call_swap4_y_x_po_1 : 
  (x: Z)
  (y: Z)
  (Pre1: `x = 3`)
  (y0: Z)
  (x0: Z)
  (Post1: `y0 = x` /\ `x0 = y`)
  `y0 = 3`.
Proof.
Intuition.
Save.

Definition call_swap4_y_x (* validation *)
  : (tmp: Z)(x: Z)(y: Z)(_: `x = 3`)
    (sig_4 Z Z Z unit [tmp0: Z][x0: Z][y0: Z][result: unit](`y0 = 3`))
  := [tmp: Z; x: Z; y: Z; Pre1: `x = 3`]
       let (y0, x0, tmp0, result0, Post1) = (swap4 y x tmp) in
       (exist_4 [tmp1: Z][x1: Z][y1: Z][result1: unit]`y1 = 3` tmp0 x0 
       y0 result0 (call_swap4_y_x_po_1 x y Pre1 y0 x0 Post1)).

