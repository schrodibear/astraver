Require Why.
Require Omega.

Lemma swap1_po_1 : 
  (x: Z)
  (y: Z)
  (result: Z)
  (Post1: result = x)
  (x0: Z)
  (Post2: x0 = y)
  (y0: Z)
  (Post3: y0 = result)
  x0 = y /\ y0 = x.
Proof.
Intuition.
Save.









Definition swap1 := (* validation *)
  [x: Z]
    [y: Z]
      let (result, Post1) = (exist_1 [result: Z]result = x x
        (refl_equal ? x)) in
      let (x0, y0, result0, Post4) =
        let (x0, result0, Post2) =
          let (result0, Post2) = (exist_1 [result0: Z]result0 = y y
            (refl_equal ? y)) in
          (exist_2 [x1: Z][result1: unit]x1 = y result0 tt Post2) in
        let (y0, result1, Post3) =
          let (result1, Post3) = (exist_1 [result1: Z]result1 = result 
            result (refl_equal ? result)) in
          (exist_2 [y1: Z][result2: unit]y1 = result result1 tt Post3) in
        (exist_3 [x1: Z][y1: Z][result2: unit]x1 = y /\ y1 = x x0 y0 
        result1 (swap1_po_1 x y result Post1 x0 Post2 y0 Post3)) in
      (exist_3 [x1: Z][y1: Z][result1: unit]x1 = y /\ y1 = x x0 y0 result0
      Post4).

Lemma swap2_po_1 : 
  (x: Z)
  (y: Z)
  (result: Z)
  (Post1: result = x)
  (x0: Z)
  (Post2: x0 = y)
  (y0: Z)
  (Post3: y0 = result)
  x0 = y /\ y0 = x.
Proof.
Intuition.
Save.









Definition swap2 := (* validation *)
  [x: Z]
    [y: Z]
      let (x0, y0, result, Post4) =
        let (result, Post1) = (exist_1 [result: Z]result = x x
          (refl_equal ? x)) in
        let (x0, y0, result0, Post5) =
          let (x0, result0, Post2) =
            let (result0, Post2) = (exist_1 [result0: Z]result0 = y y
              (refl_equal ? y)) in
            (exist_2 [x1: Z][result1: unit]x1 = y result0 tt Post2) in
          let (y0, result1, Post3) =
            let (result1, Post3) =
              (exist_1 [result1: Z]result1 = result result
              (refl_equal ? result)) in
            (exist_2 [y1: Z][result2: unit]y1 = result result1 tt Post3) in
          (exist_3 [x1: Z][y1: Z][result2: unit]x1 = y /\ y1 = x x0 y0
          result1 (swap2_po_1 x y result Post1 x0 Post2 y0 Post3)) in
        (exist_3 [x1: Z][y1: Z][result1: unit]x1 = y /\ y1 = x x0 y0 
        result0 Post5) in
      (exist_3 [x1: Z][y1: Z][result0: unit]x1 = y /\ y1 = x x0 y0 result
      Post4).

Lemma swap3_po_1 : 
  (a: Z)
  (b: Z)
  (result: Z)
  (Post1: result = a)
  (a0: Z)
  (Post2: a0 = b)
  (b0: Z)
  (Post3: b0 = result)
  a0 = b /\ b0 = a.
Proof.
Intuition.
Save.









Definition swap3 := (* validation *)
  [a: Z]
    [b: Z]
      let (result, Post1) = (exist_1 [result: Z]result = a a
        (refl_equal ? a)) in
      let (a0, b0, result0, Post4) =
        let (a0, result0, Post2) =
          let (result0, Post2) = (exist_1 [result0: Z]result0 = b b
            (refl_equal ? b)) in
          (exist_2 [a1: Z][result1: unit]a1 = b result0 tt Post2) in
        let (b0, result1, Post3) =
          let (result1, Post3) = (exist_1 [result1: Z]result1 = result 
            result (refl_equal ? result)) in
          (exist_2 [b1: Z][result2: unit]b1 = result result1 tt Post3) in
        (exist_3 [a1: Z][b1: Z][result2: unit]a1 = b /\ b1 = a a0 b0 
        result1 (swap3_po_1 a b result Post1 a0 Post2 b0 Post3)) in
      (exist_3 [a1: Z][b1: Z][result1: unit]a1 = b /\ b1 = a a0 b0 result0
      Post4).

Lemma test_swap3_po_1 : 
  (result: Z)
  (Post1: result = `1`)
  (result0: Z)
  (Post2: result0 = `2`)
  (c0: Z)
  (d0: Z)
  (Post4: c0 = result0 /\ d0 = result)
  d0 = `1`.
Proof. (* test_swap3_po_1 *)
Intuition.
Save.

















Definition test_swap3 := (* validation *)
  let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
    (refl_equal ? `1`)) in
  let (c0, result0) =
    let (result0, Post2) = (exist_1 [result0: Z]result0 = `2` `2`
      (refl_equal ? `2`)) in
    let (c0, d0, result1, Post3) =
      let (c0, d0, result2, Post4) = (swap3 result result0) in
      (exist_3 [c1: Z][d1: Z][result3: unit]d1 = `1` c0 d0 result2
      (test_swap3_po_1 result Post1 result0 Post2 c0 d0 Post4)) in
    (Build_tuple_2 c0 result1) in
  result0.

Definition call_swap3_x_y := (* validation *)
  [x: Z]
    [y: Z]
      let (x0, y0, result0, Post1) = (swap3 x y) in
      (exist_3 [x1: Z][y1: Z][result1: unit]x1 = y /\ y1 = x x0 y0 result0
      Post1).

Lemma call_swap3_y_x_po_1 : 
  (x: Z)
  (y: Z)
  (y0: Z)
  (x0: Z)
  (Post1: y0 = x /\ x0 = y)
  x0 = y /\ y0 = x.
Proof. (* call_swap3_y_x_po_1 *)
Intuition.
Save.









Definition call_swap3_y_x := (* validation *)
  [x: Z]
    [y: Z]
      let (y0, x0, result0, Post1) = (swap3 y x) in
      (exist_3 [x1: Z][y1: Z][result1: unit]x1 = y /\ y1 = x x0 y0 result0
      (call_swap3_y_x_po_1 x y y0 x0 Post1)).

Lemma swap4_po_1 : 
  (a: Z)
  (b: Z)
  (tmp0: Z)
  (Post1: tmp0 = a)
  (a0: Z)
  (Post2: a0 = b)
  (b0: Z)
  (Post3: b0 = tmp0)
  a0 = b /\ b0 = a.
Proof.
Intuition.
Save.









Definition swap4 := (* validation *)
  [a: Z]
    [b: Z]
      [tmp: Z]
        let (tmp0, result, Post1) =
          let (result, Post1) = (exist_1 [result: Z]result = a a
            (refl_equal ? a)) in
          (exist_2 [tmp1: Z][result0: unit]tmp1 = a result tt Post1) in
        let (a0, result0, Post2) =
          let (result0, Post2) = (exist_1 [result0: Z]result0 = b b
            (refl_equal ? b)) in
          (exist_2 [a1: Z][result1: unit]a1 = b result0 tt Post2) in
        let (b0, result1, Post3) =
          let (result1, Post3) = (exist_1 [result1: Z]result1 = tmp0 
            tmp0 (refl_equal ? tmp0)) in
          (exist_2 [b1: Z][result2: unit]b1 = tmp0 result1 tt Post3) in
        (exist_4 [a1: Z][b1: Z][tmp1: Z][result2: unit]a1 = b /\ b1 = a 
        a0 b0 tmp0 result1 (swap4_po_1 a b tmp0 Post1 a0 Post2 b0 Post3)).

Lemma test_swap4_po_1 : 
  (result: Z)
  (Post1: result = `1`)
  (result0: Z)
  (Post2: result0 = `2`)
  (c0: Z)
  (d0: Z)
  (Post4: c0 = result0 /\ d0 = result)
  d0 = `1`.
Proof. (* test_swap4_po_1 *)
Intuition.
Save.









Definition test_swap4 := (* validation *)
  [tmp: Z]
    let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
      (refl_equal ? `1`)) in
    let (c0, tmp0, result0) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = `2` `2`
        (refl_equal ? `2`)) in
      let (c0, d0, tmp0, result1, Post3) =
        let (c0, d0, tmp0, result2, Post4) = (swap4 result result0 tmp) in
        (exist_4 [c1: Z][d1: Z][tmp1: Z][result3: unit]d1 = `1` c0 d0 
        tmp0 result2
        (test_swap4_po_1 result Post1 result0 Post2 c0 d0 Post4)) in
      (Build_tuple_3 c0 tmp0 result1) in
    (Build_tuple_2 tmp0 result0).

Lemma call_swap4_x_y_po_1 : 
  (x: Z)
  (y: Z)
  (Pre1: x = `3`)
  (x0: Z)
  (y0: Z)
  (Post1: x0 = y /\ y0 = x)
  y0 = `3`.
Proof.
Intuition.
Save.









Definition call_swap4_x_y := (* validation *)
  [tmp: Z]
    [x: Z]
      [y: Z]
        [Pre1: x = `3`]
          let (x0, y0, tmp0, result0, Post1) = (swap4 x y tmp) in
          (exist_4 [tmp1: Z][x1: Z][y1: Z][result1: unit]y1 = `3` tmp0 
          x0 y0 result0 (call_swap4_x_y_po_1 x y Pre1 x0 y0 Post1)).

Lemma call_swap4_y_x_po_1 : 
  (x: Z)
  (y: Z)
  (Pre1: x = `3`)
  (y0: Z)
  (x0: Z)
  (Post1: y0 = x /\ x0 = y)
  y0 = `3`.
Proof.
Intuition.
Save.









Definition call_swap4_y_x := (* validation *)
  [tmp: Z]
    [x: Z]
      [y: Z]
        [Pre1: x = `3`]
          let (y0, x0, tmp0, result0, Post1) = (swap4 y x tmp) in
          (exist_4 [tmp1: Z][x1: Z][y1: Z][result1: unit]y1 = `3` tmp0 
          x0 y0 result0 (call_swap4_y_x_po_1 x y Pre1 y0 x0 Post1)).

