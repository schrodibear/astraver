(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

Definition f1 := (* validation *)
  [_: unit; x: Z]
    let (result, Post1) = (exist_1 [result: Z]`result = 0` `0`
      (refl_equal ? `0`)) in
    (exist_2 [x1: Z][result0: unit]`x1 = 0` result tt Post1).

Lemma f2_po_1 : 
  (x: Z)
  (Pre1: `x = 0`)
  `x + 1 = 1`.
Proof.
Intuition.
Save.

Definition f2 := (* validation *)
  [_: unit; x: Z; Pre1: `x = 0`]
    let (result, Post1) = (exist_1 [result: Z]`result = 1` `x + 1`
      (f2_po_1 x Pre1)) in
    (exist_2 [x1: Z][result0: unit]`x1 = 1` result tt Post1).

Lemma f3_po_1 : 
  (x: Z)
  (Pre1: `x = 0`)
  `x + 1 = 1`.
Proof.
Intuition.
Save.

Definition f3 := (* validation *)
  [_: unit; x: Z; Pre1: `x = 0`]
    let (result, Post1) = (exist_1 [result: Z]`result = 1` `x + 1`
      (f3_po_1 x Pre1)) in
    (exist_2 [x1: Z][result0: unit]`x1 = 1` result tt Post1).

Lemma f4_po_1 : 
  (x: Z)
  (Pre1: `x = 0`)
  (c_aux_1: Z)
  (Post2: c_aux_1 = x)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  `x0 = 1` /\ `c_aux_1 = 0`.
Proof.
Intuition.
Save.

Definition f4 := (* validation *)
  [_: unit; x: Z; y: Z; Pre1: `x = 0`]
    let (x0, result, Post3) =
      let (c_aux_1, Post2) = (exist_1 [result: Z]result = x x
        (refl_equal ? x)) in
      let (x0, result, Post4) =
        let (x0, result, Post1) =
          let (result, Post1) = (exist_1 [result: Z]result = `x + 1` 
            `x + 1` (refl_equal ? `x + 1`)) in
          (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
        let (result0, Post5) = (exist_1 [result0: Z]`x0 = 1` /\
          `result0 = 0` c_aux_1 (f4_po_1 x Pre1 c_aux_1 Post2 x0 Post1)) in
        (exist_2 [x1: Z][result1: Z]`x1 = 1` /\ `result1 = 0` x0 result0
        Post5) in
      (exist_2 [x1: Z][result0: Z]`x1 = 1` /\ `result0 = 0` x0 result Post4) in
    (exist_3 [x1: Z][y1: Z][result0: unit]`x1 = 1` /\ `y1 = 0` x0 result 
    tt Post3).

Lemma f5_po_1 : 
  (x: Z)
  (Pre1: `x = 0`)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  `x0 = 1` /\ `x0 = 1`.
Proof.
Intuition.
Save.

Definition f5 := (* validation *)
  [_: unit; x: Z; y: Z; Pre1: `x = 0`]
    let (x0, result, Post2) =
      let (x0, result, Post1) =
        let (result, Post1) = (exist_1 [result: Z]result = `x + 1` `x + 1`
          (refl_equal ? `x + 1`)) in
        (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
      let (result0, Post3) = (exist_1 [result0: Z]`x0 = 1` /\
        `result0 = 1` x0 (f5_po_1 x Pre1 x0 Post1)) in
      (exist_2 [x1: Z][result1: Z]`x1 = 1` /\ `result1 = 1` x0 result0 Post3) in
    (exist_3 [x1: Z][y1: Z][result0: unit]`x1 = 1` /\ `y1 = 1` x0 result 
    tt Post2).

Lemma f6_po_1 : 
  (x: Z)
  (Pre1: `x = 1`)
  `x + 2 = 3`.
Proof.
Intuition.
Save.

Definition f6 := (* validation *)
  [_: unit; x: Z; Pre1: `x = 1`]
    let (result, Post1) = (exist_1 [result: Z]`result = 3` `x + 2`
      (f6_po_1 x Pre1)) in
    (exist_2 [x1: Z][result0: unit]`x1 = 3` result tt Post1).

Lemma f7a_po_1 : 
  (x: Z)
  (Pre1: `x = 0`)
  (Test1: `x <> 0`)
  `2 = 1`.
Proof.
Intuition.
Save.

Definition f7a := (* validation *)
  [_: unit; x: Z; y: Z; Pre1: `x = 0`]
    let (result, Post2) =
      let (result, Bool1) =
        let (result1, Post3) = (Z_eq_bool x `0`) in
        (exist_1 [result2: bool]
        (if result2 then `x = 0` else `x <> 0`) result1 Post3) in
      (Cases (btest [result:bool](if result then `x = 0` else `x <> 0`)
              result Bool1) of
      | (left Test2) =>
          let (result0, Post5) = (exist_1 [result0: Z]`result0 = 1` `1`
            (refl_equal ? `1`)) in
          (exist_1 [result1: Z]`result1 = 1` result0 Post5)
      | (right Test1) =>
          let (result0, Post4) = (exist_1 [result0: Z]`result0 = 1` `2`
            (f7a_po_1 x Pre1 Test1)) in
          (exist_1 [result1: Z]`result1 = 1` result0 Post4) end) in
    (exist_2 [y1: Z][result0: unit]`y1 = 1` result tt Post2).

Lemma f7b_po_1 : 
  (x: Z)
  (Pre1: `x <> 0`)
  (Test2: `x = 0`)
  `1 = 2`.
Proof.
Intuition.
Save.

Definition f7b := (* validation *)
  [_: unit; x: Z; y: Z; Pre1: `x <> 0`]
    let (result, Post2) =
      let (result, Bool1) =
        let (result1, Post3) = (Z_eq_bool x `0`) in
        (exist_1 [result2: bool]
        (if result2 then `x = 0` else `x <> 0`) result1 Post3) in
      (Cases (btest [result:bool](if result then `x = 0` else `x <> 0`)
              result Bool1) of
      | (left Test2) =>
          let (result0, Post5) = (exist_1 [result0: Z]`result0 = 2` `1`
            (f7b_po_1 x Pre1 Test2)) in
          (exist_1 [result1: Z]`result1 = 2` result0 Post5)
      | (right Test1) =>
          let (result0, Post4) = (exist_1 [result0: Z]`result0 = 2` `2`
            (refl_equal ? `2`)) in
          (exist_1 [result1: Z]`result1 = 2` result0 Post4) end) in
    (exist_2 [y1: Z][result0: unit]`y1 = 2` result tt Post2).

Lemma t1_po_1 : 
  (t: (array Z))
  (Pre2: `(array_length t) = 10` /\ `(access t 0) = 1`)
  `0 <= 0` /\ `0 < (array_length t)`.
Proof.
Intuition.
Save.

Lemma t1_po_2 : 
  (t: (array Z))
  (Pre2: `(array_length t) = 10` /\ `(access t 0) = 1`)
  (Pre1: `0 <= 0` /\ `0 < (array_length t)`)
  `(access t 0) = 1`.
Proof.
Intuition.
Save.

Definition t1 := (* validation *)
  [_: unit; t: (array Z); y: Z; Pre2: `(array_length t) = 10` /\
   `(access t 0) = 1`]
    let Pre1 = (t1_po_1 t Pre2) in
    let (result, Post1) = (exist_1 [result: Z]`result = 1` (access t `0`)
      (t1_po_2 t Pre2 Pre1)) in
    (exist_2 [y1: Z][result0: unit]`y1 = 1` result tt Post1).

Lemma t2_po_1 : 
  (t: (array Z))
  (x: Z)
  (Pre2: `(array_length t) = 10` /\ `x = 0` /\ `(access t 0) = 1`)
  (c_aux_2: Z)
  (Post2: c_aux_2 = x)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  `(access t c_aux_2) = 1` /\ `0 <= c_aux_2` /\ `c_aux_2 < (array_length t)`.
Proof.
Intuition.
Subst c_aux_2 x; Auto.
Save.

Lemma t2_po_2 : 
  (t: (array Z))
  (x: Z)
  (Pre2: `(array_length t) = 10` /\ `x = 0` /\ `(access t 0) = 1`)
  (aux_1: Z)
  (Post4: `(access t aux_1) = 1` /\ `0 <= aux_1` /\
          `aux_1 < (array_length t)`)
  `0 <= aux_1` /\ `aux_1 < (array_length t)`.
Proof.
Intuition.
Save.

Definition t2 := (* validation *)
  [_: unit; t: (array Z); x: Z; y: Z; Pre2: `(array_length t) = 10` /\
   `x = 0` /\ `(access t 0) = 1`]
    let (x0, result, Post3) =
      let (x0, aux_1, Post4) =
        let (c_aux_2, Post2) = (exist_1 [result: Z]result = x x
          (refl_equal ? x)) in
        let (x0, result, Post5) =
          let (x0, result, Post1) =
            let (result, Post1) = (exist_1 [result: Z]
              result = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
            (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
          let (result0, Post6) = (exist_1 [result0: Z]
            `(access t result0) = 1` /\ `0 <= result0` /\
            `result0 < (array_length t)` c_aux_2
            (t2_po_1 t x Pre2 c_aux_2 Post2 x0 Post1)) in
          (exist_2 [x1: Z][result1: Z]`(access t result1) = 1` /\
          `0 <= result1` /\ `result1 < (array_length t)` x0 result0 Post6) in
        (exist_2 [x1: Z][result0: Z]`(access t result0) = 1` /\
        `0 <= result0` /\ `result0 < (array_length t)` x0 result Post5) in
      let Pre1 = (t2_po_2 t x Pre2 aux_1 Post4) in
      let (result, Post7) =
        let (result, Post8) = (exist_1 [result: Z]
          `(access t result) = 1` aux_1 (proj1 ? ? Post4)) in
        (exist_1 [result0: Z]`result0 = 1` (access t result) Post8) in
      (exist_2 [x1: Z][result0: Z]`result0 = 1` x0 result Post7) in
    (exist_3 [x1: Z][y1: Z][result0: unit]`y1 = 1` x0 result tt Post3).

Lemma e1_po_1 : 
  (x: Z)
  (Pre1: `x = 2`)
  (c_aux_3: Z)
  (Post3: c_aux_3 = x)
  (c_aux_4: Z)
  (Post2: c_aux_4 = x)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  `c_aux_3 + c_aux_4 = 4`.
Proof.
Intuition.
Save.

Definition e1 := (* validation *)
  [_: unit; x: Z; y: Z; Pre1: `x = 2`]
    let (x0, result, Post4) =
      let (c_aux_3, Post3) = (exist_1 [result: Z]result = x x
        (refl_equal ? x)) in
      let (x0, result, Post5) =
        let (x0, c_aux_5, Post6) =
          let (c_aux_4, Post2) = (exist_1 [result: Z]result = x x
            (refl_equal ? x)) in
          let (x0, result, Post7) =
            let (x0, result, Post1) =
              let (result, Post1) = (exist_1 [result: Z]
                result = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
              (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
            let (result0, Post8) = (exist_1 [result0: Z]
              `c_aux_3 + result0 = 4` c_aux_4
              (e1_po_1 x Pre1 c_aux_3 Post3 c_aux_4 Post2 x0 Post1)) in
            (exist_2 [x1: Z][result1: Z]`c_aux_3 + result1 = 4` x0 result0
            Post8) in
          (exist_2 [x1: Z][result0: Z]`c_aux_3 + result0 = 4` x0 result
          Post7) in
        let (result, Post9) = (exist_1 [result: Z]
          `result = 4` `c_aux_3 + c_aux_5` Post6) in
        (exist_2 [x1: Z][result0: Z]`result0 = 4` x0 result Post9) in
      (exist_2 [x1: Z][result0: Z]`result0 = 4` x0 result Post5) in
    (exist_3 [x1: Z][y1: Z][result0: unit]`y1 = 4` x0 result tt Post4).

Lemma e2_po_1 : 
  (x: Z)
  (Pre1: `x = 2`)
  (c_aux_6: Z)
  (Post2: c_aux_6 = x)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  `c_aux_6 + x0 = 5`.
Proof.
Intuition.
Save.

Definition e2 := (* validation *)
  [_: unit; x: Z; y: Z; Pre1: `x = 2`]
    let (x0, result, Post3) =
      let (c_aux_6, Post2) = (exist_1 [result: Z]result = x x
        (refl_equal ? x)) in
      let (x0, result, Post4) =
        let (x0, c_aux_7, Post5) =
          let (x0, result, Post1) =
            let (result, Post1) = (exist_1 [result: Z]
              result = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
            (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
          let (result0, Post6) = (exist_1 [result0: Z]
            `c_aux_6 + result0 = 5` x0
            (e2_po_1 x Pre1 c_aux_6 Post2 x0 Post1)) in
          (exist_2 [x1: Z][result1: Z]`c_aux_6 + result1 = 5` x0 result0
          Post6) in
        let (result, Post7) = (exist_1 [result: Z]
          `result = 5` `c_aux_6 + c_aux_7` Post5) in
        (exist_2 [x1: Z][result0: Z]`result0 = 5` x0 result Post7) in
      (exist_2 [x1: Z][result0: Z]`result0 = 5` x0 result Post4) in
    (exist_3 [x1: Z][y1: Z][result0: unit]`y1 = 5` x0 result tt Post3).

Lemma e3_po_1 : 
  (x: Z)
  (Pre1: `x = 2`)
  (c_aux_8: Z)
  (Post2: c_aux_8 = x)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  ((result:Z) (result = x0 -> `c_aux_8 + result = 5`)).
Proof.
Intuition.
Save.

Lemma e3_po_2 : 
  (x: Z)
  (Pre1: `x = 2`)
  (x0: Z)
  (c_aux_9: Z)
  (Post5: ((result:Z) (result = x0 -> `c_aux_9 + result = 5`)))
  (c_aux_10: Z)
  (Post3: c_aux_10 = x0)
  `c_aux_9 + c_aux_10 = 5`.
Proof.
Intuition.
Save.

Definition e3 := (* validation *)
  [_: unit; x: Z; y: Z; Pre1: `x = 2`]
    let (x0, result, Post4) =
      let (x0, c_aux_9, Post5) =
        let (c_aux_8, Post2) = (exist_1 [result: Z]result = x x
          (refl_equal ? x)) in
        let (x0, result, Post6) =
          let (x0, result, Post1) =
            let (result, Post1) = (exist_1 [result: Z]
              result = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
            (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
          let (result0, Post7) = (exist_1 [result0: Z]
            ((result:Z) (result = x0 -> `result0 + result = 5`)) c_aux_8
            (e3_po_1 x Pre1 c_aux_8 Post2 x0 Post1)) in
          (exist_2 [x1: Z][result1: Z]
          ((result:Z) (result = x1 -> `result1 + result = 5`)) x0 result0
          Post7) in
        (exist_2 [x1: Z][result0: Z]
        ((result:Z) (result = x1 -> `result0 + result = 5`)) x0 result Post6) in
      let (result, Post8) =
        let (c_aux_10, Post3) = (exist_1 [result: Z]result = x0 x0
          (refl_equal ? x0)) in
        let (result, Post9) = (exist_1 [result: Z]
          `result = 5` `c_aux_9 + c_aux_10`
          (e3_po_2 x Pre1 x0 c_aux_9 Post5 c_aux_10 Post3)) in
        (exist_1 [result0: Z]`result0 = 5` result Post9) in
      (exist_2 [x1: Z][result0: Z]`result0 = 5` x0 result Post8) in
    (exist_3 [x1: Z][y1: Z][result0: unit]`y1 = 5` x0 result tt Post4).

Lemma e4_po_1 : 
  (x: Z)
  (Pre1: `x = 2`)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  ((result:Z) (result = x0 -> `x0 + result = 6`)).
Proof.
Intuition.
Save.

Lemma e4_po_2 : 
  (x: Z)
  (Pre1: `x = 2`)
  (x0: Z)
  (c_aux_11: Z)
  (Post4: ((result:Z) (result = x0 -> `c_aux_11 + result = 6`)))
  (c_aux_12: Z)
  (Post2: c_aux_12 = x0)
  `c_aux_11 + c_aux_12 = 6`.
Proof.
Intuition.
Save.

Definition e4 := (* validation *)
  [_: unit; x: Z; y: Z; Pre1: `x = 2`]
    let (x0, result, Post3) =
      let (x0, c_aux_11, Post4) =
        let (x0, result, Post1) =
          let (result, Post1) = (exist_1 [result: Z]result = `x + 1` 
            `x + 1` (refl_equal ? `x + 1`)) in
          (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
        let (result0, Post5) = (exist_1 [result0: Z]
          ((result:Z) (result = x0 -> `result0 + result = 6`)) x0
          (e4_po_1 x Pre1 x0 Post1)) in
        (exist_2 [x1: Z][result1: Z]
        ((result:Z) (result = x1 -> `result1 + result = 6`)) x0 result0
        Post5) in
      let (result, Post6) =
        let (c_aux_12, Post2) = (exist_1 [result: Z]result = x0 x0
          (refl_equal ? x0)) in
        let (result, Post7) = (exist_1 [result: Z]
          `result = 6` `c_aux_11 + c_aux_12`
          (e4_po_2 x Pre1 x0 c_aux_11 Post4 c_aux_12 Post2)) in
        (exist_1 [result0: Z]`result0 = 6` result Post7) in
      (exist_2 [x1: Z][result0: Z]`result0 = 6` x0 result Post6) in
    (exist_3 [x1: Z][y1: Z][result0: unit]`y1 = 6` x0 result tt Post3).

Lemma e5_po_1 : 
  (x: Z)
  (Pre1: `x = 2`)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  ((result:Z) (result = x0 -> ((x:Z) (x = `x0 + 1` -> `x0 + result = 6`)))).
Proof.
Intuition.
Save.

Lemma e5_po_2 : 
  (x: Z)
  (Pre1: `x = 2`)
  (x0: Z)
  (c_aux_13: Z)
  (Post5: ((result:Z)
           (result = x0 -> ((x:Z) (x = `x0 + 1` -> `c_aux_13 + result = 6`)))))
  (c_aux_14: Z)
  (Post3: c_aux_14 = x0)
  (x1: Z)
  (Post2: x1 = `x0 + 1`)
  `c_aux_13 + c_aux_14 = 6`.
Proof.
Intuition.
Save.

Definition e5 := (* validation *)
  [_: unit; x: Z; y: Z; Pre1: `x = 2`]
    let (x0, result, Post4) =
      let (x0, c_aux_13, Post5) =
        let (x0, result, Post1) =
          let (result, Post1) = (exist_1 [result: Z]result = `x + 1` 
            `x + 1` (refl_equal ? `x + 1`)) in
          (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
        let (result0, Post6) = (exist_1 [result0: Z]
          ((result:Z)
           (result = x0 -> ((x:Z) (x = `x0 + 1` -> `result0 + result = 6`)))) 
          x0 (e5_po_1 x Pre1 x0 Post1)) in
        (exist_2 [x1: Z][result1: Z]
        ((result:Z)
         (result = x1 -> ((x:Z) (x = `x1 + 1` -> `result1 + result = 6`)))) 
        x0 result0 Post6) in
      let (x1, result, Post7) =
        let (x1, c_aux_15, Post8) =
          let (c_aux_14, Post3) = (exist_1 [result: Z]result = x0 x0
            (refl_equal ? x0)) in
          let (x1, result, Post9) =
            let (x1, result, Post2) =
              let (result, Post2) = (exist_1 [result: Z]
                result = `x0 + 1` `x0 + 1` (refl_equal ? `x0 + 1`)) in
              (exist_2 [x2: Z][result0: unit]x2 = `x0 + 1` result tt Post2) in
            let (result0, Post10) = (exist_1 [result0: Z]
              `c_aux_13 + result0 = 6` c_aux_14
              (e5_po_2 x Pre1 x0 c_aux_13 Post5 c_aux_14 Post3 x1 Post2)) in
            (exist_2 [x2: Z][result1: Z]`c_aux_13 + result1 = 6` x1 result0
            Post10) in
          (exist_2 [x2: Z][result0: Z]`c_aux_13 + result0 = 6` x1 result
          Post9) in
        let (result, Post11) = (exist_1 [result: Z]
          `result = 6` `c_aux_13 + c_aux_15` Post8) in
        (exist_2 [x2: Z][result0: Z]`result0 = 6` x1 result Post11) in
      (exist_2 [x2: Z][result0: Z]`result0 = 6` x1 result Post7) in
    (exist_3 [x1: Z][y1: Z][result0: unit]`y1 = 6` x0 result tt Post4).

