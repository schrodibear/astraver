(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

Definition f1 (* validation *)
  : (_: unit)(x: Z)(sig_2 Z unit [x0: Z][result: unit](`x0 = 0`))
  := [_: unit; x: Z]
       let (result, Post1) = (exist_1 [result: Z]`result = 0` `0`
         (refl_equal ? `0`)) in
       (exist_2 [x1: Z][result0: unit]`x1 = 0` result tt Post1).

(* Why obligation from file "good-c/all.c", characters 117-120 *)
Lemma f2_po_1 : 
  (x: Z)
  (Pre1: `x = 0`)
  `x + 1 = 1`.
Proof.
Intuition.
Save.

Definition f2 (* validation *)
  : (_: unit)(x: Z)(_: `x = 0`)(sig_2 Z unit [x0: Z][result: unit](`x0 = 1`))
  := [_: unit; x: Z; Pre1: `x = 0`]
       let (result, Post1) = (exist_1 [result: Z]`result = 1` `x + 1`
         (f2_po_1 x Pre1)) in
       (exist_2 [x1: Z][result0: unit]`x1 = 1` result tt Post1).

(* Why obligation from file "good-c/all.c", characters 163-166 *)
Lemma f3_po_1 : 
  (x: Z)
  (Pre1: `x = 0`)
  `x + 1 = 1`.
Proof.
Intuition.
Save.

Definition f3 (* validation *)
  : (_: unit)(x: Z)(_: `x = 0`)(sig_2 Z unit [x0: Z][result: unit](`x0 = 1`))
  := [_: unit; x: Z; Pre1: `x = 0`]
       let (result, Post1) = (exist_1 [result: Z]`result = 1` `x + 1`
         (f3_po_1 x Pre1)) in
       (exist_2 [x1: Z][result0: unit]`x1 = 1` result tt Post1).

(* Why obligation from file "good-c/all.c", characters 213-216 *)
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

Definition f4 (* validation *)
  : (_: unit)(x: Z)(y: Z)(_: `x = 0`)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`x0 = 1` /\ `y0 = 0`))
  := [_: unit; x: Z; y: Z; Pre1: `x = 0`]
       let (x0, result, Post3) =
         let (c_aux_1, Post2) = (exist_1 [result: Z]result = x x
           (refl_equal ? x)) in
         let (x0, result, Post4) =
           let (x0, result, Post1) =
             let (result, Post1) = (exist_1 [result: Z]
               result = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
             (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
           let (result0, Post5) = (exist_1 [result0: Z]`x0 = 1` /\
             `result0 = 0` c_aux_1
             (f4_po_1 x Pre1 c_aux_1 Post2 x0 Post1)) in
           (exist_2 [x1: Z][result1: Z]`x1 = 1` /\ `result1 = 0` x0 result0
           Post5) in
         (exist_2 [x1: Z][result0: Z]`x1 = 1` /\ `result0 = 0` x0 result
         Post4) in
       (exist_3 [x1: Z][y1: Z][result0: unit]`x1 = 1` /\ `y1 = 0` x0 
       result tt Post3).

(* Why obligation from file "good-c/all.c", characters 273-276 *)
Lemma f5_po_1 : 
  (x: Z)
  (Pre1: `x = 0`)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  `x0 = 1` /\ `x0 = 1`.
Proof.
Intuition.
Save.

Definition f5 (* validation *)
  : (_: unit)(x: Z)(y: Z)(_: `x = 0`)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`x0 = 1` /\ `y0 = 1`))
  := [_: unit; x: Z; y: Z; Pre1: `x = 0`]
       let (x0, result, Post2) =
         let (x0, result, Post1) =
           let (result, Post1) = (exist_1 [result: Z]result = `x + 1` 
             `x + 1` (refl_equal ? `x + 1`)) in
           (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
         let (result0, Post3) = (exist_1 [result0: Z]`x0 = 1` /\
           `result0 = 1` x0 (f5_po_1 x Pre1 x0 Post1)) in
         (exist_2 [x1: Z][result1: Z]`x1 = 1` /\ `result1 = 1` x0 result0
         Post3) in
       (exist_3 [x1: Z][y1: Z][result0: unit]`x1 = 1` /\ `y1 = 1` x0 
       result tt Post2).

(* Why obligation from file "good-c/all.c", characters 329-335 *)
Lemma f6_po_1 : 
  (x: Z)
  (Pre1: `x = 1`)
  `x + 2 = 3`.
Proof.
Intuition.
Save.

Definition f6 (* validation *)
  : (_: unit)(x: Z)(_: `x = 1`)(sig_2 Z unit [x0: Z][result: unit](`x0 = 3`))
  := [_: unit; x: Z; Pre1: `x = 1`]
       let (result, Post1) = (exist_1 [result: Z]`result = 3` `x + 2`
         (f6_po_1 x Pre1)) in
       (exist_2 [x1: Z][result0: unit]`x1 = 3` result tt Post1).

(* Why obligation from file "good-c/all.c", characters 396-397 *)
Lemma f7a_po_1 : 
  (x: Z)
  (Pre1: `x = 0`)
  (Test1: `x <> 0`)
  `2 = 1`.
Proof.
Intuition.
Save.

Definition f7a (* validation *)
  : (_: unit)(x: Z)(y: Z)(_: `x = 0`)
    (sig_2 Z unit [y0: Z][result: unit](`y0 = 1`))
  := [_: unit; x: Z; y: Z; Pre1: `x = 0`]
       let (result, Post2) =
         let (result, Bool1) =
           let (result1, Post3) = (Z_eq_bool x `0`) in
           (exist_1 [result2: bool]
           (if result2 then `x = 0` else `x <> 0`) result1 Post3) in
         (Cases (btest [result:bool](if result then `x = 0` else `x <> 0`)
                 result Bool1) of
         | (left Test2) =>
             let (result0, Post5) = (exist_1 [result0: Z]`result0 = 1` 
               `1` (refl_equal ? `1`)) in
             (exist_1 [result1: Z]`result1 = 1` result0 Post5)
         | (right Test1) =>
             let (result0, Post4) = (exist_1 [result0: Z]`result0 = 1` 
               `2` (f7a_po_1 x Pre1 Test1)) in
             (exist_1 [result1: Z]`result1 = 1` result0 Post4) end) in
       (exist_2 [y1: Z][result0: unit]`y1 = 1` result tt Post2).

(* Why obligation from file "good-c/all.c", characters 454-455 *)
Lemma f7b_po_1 : 
  (x: Z)
  (Pre1: `x <> 0`)
  (Test2: `x = 0`)
  `1 = 2`.
Proof.
Intuition.
Save.

Definition f7b (* validation *)
  : (_: unit)(x: Z)(y: Z)(_: `x <> 0`)
    (sig_2 Z unit [y0: Z][result: unit](`y0 = 2`))
  := [_: unit; x: Z; y: Z; Pre1: `x <> 0`]
       let (result, Post2) =
         let (result, Bool1) =
           let (result1, Post3) = (Z_eq_bool x `0`) in
           (exist_1 [result2: bool]
           (if result2 then `x = 0` else `x <> 0`) result1 Post3) in
         (Cases (btest [result:bool](if result then `x = 0` else `x <> 0`)
                 result Bool1) of
         | (left Test2) =>
             let (result0, Post5) = (exist_1 [result0: Z]`result0 = 2` 
               `1` (f7b_po_1 x Pre1 Test2)) in
             (exist_1 [result1: Z]`result1 = 2` result0 Post5)
         | (right Test1) =>
             let (result0, Post4) = (exist_1 [result0: Z]`result0 = 2` 
               `2` (refl_equal ? `2`)) in
             (exist_1 [result1: Z]`result1 = 2` result0 Post4) end) in
       (exist_2 [y1: Z][result0: unit]`y1 = 2` result tt Post2).

(* Why obligation from file "good-c/all.c", characters 544-548 *)
Lemma t1_po_1 : 
  (t: (array Z))
  (Pre2: `(array_length t) = 10` /\ `(access t 0) = 1`)
  `0 <= 0` /\ `0 < (array_length t)`.
Proof.
Intuition.
Save.

(* Why obligation from file "good-c/all.c", characters 544-548 *)
Lemma t1_po_2 : 
  (t: (array Z))
  (Pre2: `(array_length t) = 10` /\ `(access t 0) = 1`)
  (Pre1: `0 <= 0` /\ `0 < (array_length t)`)
  `(access t 0) = 1`.
Proof.
Intuition.
Save.

Definition t1 (* validation *)
  : (_: unit)(t: (array Z))(y: Z)(_: `(array_length t) = 10` /\
    `(access t 0) = 1`)(sig_2 Z unit [y0: Z][result: unit](`y0 = 1`))
  := [_: unit; t: (array Z); y: Z; Pre2: `(array_length t) = 10` /\
      `(access t 0) = 1`]
       let Pre1 = (t1_po_1 t Pre2) in
       let (result, Post1) = (exist_1 [result: Z]`result = 1` (access t `0`)
         (t1_po_2 t Pre2 Pre1)) in
       (exist_2 [y1: Z][result0: unit]`y1 = 1` result tt Post1).

(* Why obligation from file "good-c/all.c", characters 635-638 *)
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

(* Why obligation from file "good-c/all.c", characters 633-639 *)
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

Definition t2 (* validation *)
  : (_: unit)(t: (array Z))(x: Z)(y: Z)(_: `(array_length t) = 10` /\
    `x = 0` /\ `(access t 0) = 1`)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`y0 = 1`))
  := [_: unit; t: (array Z); x: Z; y: Z; Pre2: `(array_length t) = 10` /\
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

(* Why obligation from file "good-c/all.c", characters 726-729 *)
Lemma t3_po_1 : 
  (t: (array Z))
  (x: Z)
  (Pre2: `(array_length t) = 10` /\ `x = 0` /\ `(access t 1) = 1`)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  `(access t x0) = 1` /\ `0 <= x0` /\ `x0 < (array_length t)`.
Proof.
Intuition.
Replace x0 with `1`; Omega.
Save.

(* Why obligation from file "good-c/all.c", characters 724-730 *)
Lemma t3_po_2 : 
  (t: (array Z))
  (x: Z)
  (Pre2: `(array_length t) = 10` /\ `x = 0` /\ `(access t 1) = 1`)
  (aux_1: Z)
  (Post3: `(access t aux_1) = 1` /\ `0 <= aux_1` /\
          `aux_1 < (array_length t)`)
  `0 <= aux_1` /\ `aux_1 < (array_length t)`.
Proof.
Intuition.
Save.

Definition t3 (* validation *)
  : (_: unit)(t: (array Z))(x: Z)(y: Z)(_: `(array_length t) = 10` /\
    `x = 0` /\ `(access t 1) = 1`)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`y0 = 1`))
  := [_: unit; t: (array Z); x: Z; y: Z; Pre2: `(array_length t) = 10` /\
      `x = 0` /\ `(access t 1) = 1`]
       let (x0, result, Post2) =
         let (x0, aux_1, Post3) =
           let (x0, result, Post1) =
             let (result, Post1) = (exist_1 [result: Z]
               result = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
             (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
           let (result0, Post4) = (exist_1 [result0: Z]
             `(access t result0) = 1` /\ `0 <= result0` /\
             `result0 < (array_length t)` x0 (t3_po_1 t x Pre2 x0 Post1)) in
           (exist_2 [x1: Z][result1: Z]`(access t result1) = 1` /\
           `0 <= result1` /\ `result1 < (array_length t)` x0 result0 Post4) in
         let Pre1 = (t3_po_2 t x Pre2 aux_1 Post3) in
         let (result, Post5) =
           let (result, Post6) = (exist_1 [result: Z]
             `(access t result) = 1` aux_1 (proj1 ? ? Post3)) in
           (exist_1 [result0: Z]`result0 = 1` (access t result) Post6) in
         (exist_2 [x1: Z][result0: Z]`result0 = 1` x0 result Post5) in
       (exist_3 [x1: Z][y1: Z][result0: unit]`y1 = 1` x0 result tt Post2).

(* Why obligation from file "good-c/all.c", characters 821-824 *)
Lemma t4_po_1 : 
  (t: (array Z))
  (x: Z)
  (Pre2: `(array_length t) = 10` /\ `x = 2` /\ `(access t 2) = 3`)
  (c_aux_4: Z)
  (Post3: c_aux_4 = x)
  (c_aux_3: Z)
  (Post2: c_aux_3 = x)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  (`x0 = 3` /\
  `(access (store t c_aux_4 (access t c_aux_4) + c_aux_3) 2) = 5`) /\
  `0 <= c_aux_4` /\ `c_aux_4 < (array_length t)`.
Proof.
Intuition.
Subst x c_aux_3 c_aux_4.
AccessSame.
Save.

(* Why obligation from file "good-c/all.c", characters 813-824 *)
Lemma t4_po_2 : 
  (t: (array Z))
  (x: Z)
  (Pre2: `(array_length t) = 10` /\ `x = 2` /\ `(access t 2) = 3`)
  (c_aux_4: Z)
  (Post3: c_aux_4 = x)
  (x0: Z)
  (aux_3: Z)
  (Post5: (`x0 = 3` /\ `(access (store t c_aux_4 aux_3) 2) = 5`) /\
          `0 <= c_aux_4` /\ `c_aux_4 < (array_length t)`)
  (aux_2: Z)
  (Post11: (`x0 = 3` /\ `(access (store t aux_2 aux_3) 2) = 5`) /\
           `0 <= aux_2` /\ `aux_2 < (array_length t)`)
  `0 <= aux_2` /\ `aux_2 < (array_length t)`.
Proof.
Intuition.
Save.

Definition t4 (* validation *)
  : (_: unit)(t: (array Z))(x: Z)(_: `(array_length t) = 10` /\ `x = 2` /\
    `(access t 2) = 3`)
    (sig_3 (array Z) Z unit [t0: (array Z)][x0: Z][result: unit](`x0 = 3` /\
     `(access t0 2) = 5`))
  := [_: unit; t: (array Z); x: Z; Pre2: `(array_length t) = 10` /\
      `x = 2` /\ `(access t 2) = 3`]
       let (c_aux_4, Post3) = (exist_1 [result: Z]result = x x
         (refl_equal ? x)) in
       let (t0, x0, result, Post4) =
         let (x0, aux_3, Post5) =
           let (x0, aux_1, Post6) =
             let (c_aux_3, Post2) = (exist_1 [result: Z]result = x x
               (refl_equal ? x)) in
             let (x0, result, Post7) =
               let (x0, result, Post1) =
                 let (result, Post1) = (exist_1 [result: Z]
                   result = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
                 (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
               let (result0, Post8) = (exist_1 [result0: Z](`x0 = 3` /\
                 `(access (store t c_aux_4 (access t c_aux_4) + result0) 2) =
                  5`) /\ `0 <= c_aux_4` /\
                 `c_aux_4 < (array_length t)` c_aux_3
                 (t4_po_1 t x Pre2 c_aux_4 Post3 c_aux_3 Post2 x0 Post1)) in
               (exist_2 [x1: Z][result1: Z](`x1 = 3` /\
               `(access (store t c_aux_4 (access t c_aux_4) + result1) 2) = 5`) /\
               `0 <= c_aux_4` /\ `c_aux_4 < (array_length t)` x0 result0
               Post8) in
             (exist_2 [x1: Z][result0: Z](`x1 = 3` /\
             `(access (store t c_aux_4 (access t c_aux_4) + result0) 2) = 5`) /\
             `0 <= c_aux_4` /\ `c_aux_4 < (array_length t)` x0 result Post7) in
           let (result, Post9) = (exist_1 [result: Z](`x0 = 3` /\
             `(access (store t c_aux_4 result) 2) = 5`) /\ `0 <= c_aux_4` /\
             `c_aux_4 < (array_length t)` `(access t c_aux_4) + aux_1`
             Post6) in
           (exist_2 [x1: Z][result0: Z](`x1 = 3` /\
           `(access (store t c_aux_4 result0) 2) = 5`) /\ `0 <= c_aux_4` /\
           `c_aux_4 < (array_length t)` x0 result Post9) in
         let (t0, result, Post10) =
           let (aux_2, Post11) = (exist_1 [result: Z](`x0 = 3` /\
             `(access (store t result aux_3) 2) = 5`) /\ `0 <= result` /\
             `result < (array_length t)` c_aux_4 Post5) in
           let Pre1 =
             (t4_po_2 t x Pre2 c_aux_4 Post3 x0 aux_3 Post5 aux_2 Post11) in
           let (t0, result, Post12) = (exist_2 [t5: (array Z)][result1: unit]
             `x0 = 3` /\ `(access t5 2) = 5` (store t aux_2 aux_3) tt
             (proj1 ? ? Post11)) in
           (exist_2 [t5: (array Z)][result0: unit]`x0 = 3` /\
           `(access t5 2) = 5` t0 result Post12) in
         (exist_3 [t5: (array Z)][x1: Z][result0: unit]`x1 = 3` /\
         `(access t5 2) = 5` t0 x0 result Post10) in
       (exist_3 [t5: (array Z)][x1: Z][result0: unit]`x1 = 3` /\
       `(access t5 2) = 5` t0 x0 result Post4).

(* Why obligation from file "good-c/all.c", characters 913-916 *)
Lemma e1_po_1 : 
  (x: Z)
  (Pre1: `x = 2`)
  (c_aux_5: Z)
  (Post3: c_aux_5 = x)
  (c_aux_6: Z)
  (Post2: c_aux_6 = x)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  `c_aux_5 + c_aux_6 = 4`.
Proof.
Intuition.
Save.

Definition e1 (* validation *)
  : (_: unit)(x: Z)(y: Z)(_: `x = 2`)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`y0 = 4`))
  := [_: unit; x: Z; y: Z; Pre1: `x = 2`]
       let (x0, result, Post4) =
         let (c_aux_5, Post3) = (exist_1 [result: Z]result = x x
           (refl_equal ? x)) in
         let (x0, result, Post5) =
           let (x0, c_aux_7, Post6) =
             let (c_aux_6, Post2) = (exist_1 [result: Z]result = x x
               (refl_equal ? x)) in
             let (x0, result, Post7) =
               let (x0, result, Post1) =
                 let (result, Post1) = (exist_1 [result: Z]
                   result = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
                 (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
               let (result0, Post8) = (exist_1 [result0: Z]
                 `c_aux_5 + result0 = 4` c_aux_6
                 (e1_po_1 x Pre1 c_aux_5 Post3 c_aux_6 Post2 x0 Post1)) in
               (exist_2 [x1: Z][result1: Z]`c_aux_5 + result1 = 4` x0 
               result0 Post8) in
             (exist_2 [x1: Z][result0: Z]`c_aux_5 + result0 = 4` x0 result
             Post7) in
           let (result, Post9) = (exist_1 [result: Z]
             `result = 4` `c_aux_5 + c_aux_7` Post6) in
           (exist_2 [x1: Z][result0: Z]`result0 = 4` x0 result Post9) in
         (exist_2 [x1: Z][result0: Z]`result0 = 4` x0 result Post5) in
       (exist_3 [x1: Z][y1: Z][result0: unit]`y1 = 4` x0 result tt Post4).

(* Why obligation from file "good-c/all.c", characters 967-970 *)
Lemma e2_po_1 : 
  (x: Z)
  (Pre1: `x = 2`)
  (c_aux_8: Z)
  (Post2: c_aux_8 = x)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  `c_aux_8 + x0 = 5`.
Proof.
Intuition.
Save.

Definition e2 (* validation *)
  : (_: unit)(x: Z)(y: Z)(_: `x = 2`)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`y0 = 5`))
  := [_: unit; x: Z; y: Z; Pre1: `x = 2`]
       let (x0, result, Post3) =
         let (c_aux_8, Post2) = (exist_1 [result: Z]result = x x
           (refl_equal ? x)) in
         let (x0, result, Post4) =
           let (x0, c_aux_9, Post5) =
             let (x0, result, Post1) =
               let (result, Post1) = (exist_1 [result: Z]
                 result = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
               (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
             let (result0, Post6) = (exist_1 [result0: Z]
               `c_aux_8 + result0 = 5` x0
               (e2_po_1 x Pre1 c_aux_8 Post2 x0 Post1)) in
             (exist_2 [x1: Z][result1: Z]`c_aux_8 + result1 = 5` x0 result0
             Post6) in
           let (result, Post7) = (exist_1 [result: Z]
             `result = 5` `c_aux_8 + c_aux_9` Post5) in
           (exist_2 [x1: Z][result0: Z]`result0 = 5` x0 result Post7) in
         (exist_2 [x1: Z][result0: Z]`result0 = 5` x0 result Post4) in
       (exist_3 [x1: Z][y1: Z][result0: unit]`y1 = 5` x0 result tt Post3).

(* Why obligation from file "good-c/all.c", characters 1017-1020 *)
Lemma e3_po_1 : 
  (x: Z)
  (Pre1: `x = 2`)
  (c_aux_10: Z)
  (Post2: c_aux_10 = x)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  ((result:Z) (result = x0 -> `c_aux_10 + result = 5`)).
Proof.
Intuition.
Save.

(* Why obligation from file "good-c/all.c", characters 1017-1024 *)
Lemma e3_po_2 : 
  (x: Z)
  (Pre1: `x = 2`)
  (x0: Z)
  (c_aux_11: Z)
  (Post5: ((result:Z) (result = x0 -> `c_aux_11 + result = 5`)))
  (c_aux_12: Z)
  (Post3: c_aux_12 = x0)
  `c_aux_11 + c_aux_12 = 5`.
Proof.
Intuition.
Save.

Definition e3 (* validation *)
  : (_: unit)(x: Z)(y: Z)(_: `x = 2`)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`y0 = 5`))
  := [_: unit; x: Z; y: Z; Pre1: `x = 2`]
       let (x0, result, Post4) =
         let (x0, c_aux_11, Post5) =
           let (c_aux_10, Post2) = (exist_1 [result: Z]result = x x
             (refl_equal ? x)) in
           let (x0, result, Post6) =
             let (x0, result, Post1) =
               let (result, Post1) = (exist_1 [result: Z]
                 result = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
               (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
             let (result0, Post7) = (exist_1 [result0: Z]
               ((result:Z) (result = x0 -> `result0 + result = 5`)) c_aux_10
               (e3_po_1 x Pre1 c_aux_10 Post2 x0 Post1)) in
             (exist_2 [x1: Z][result1: Z]
             ((result:Z) (result = x1 -> `result1 + result = 5`)) x0 
             result0 Post7) in
           (exist_2 [x1: Z][result0: Z]
           ((result:Z) (result = x1 -> `result0 + result = 5`)) x0 result
           Post6) in
         let (result, Post8) =
           let (c_aux_12, Post3) = (exist_1 [result: Z]result = x0 x0
             (refl_equal ? x0)) in
           let (result, Post9) = (exist_1 [result: Z]
             `result = 5` `c_aux_11 + c_aux_12`
             (e3_po_2 x Pre1 x0 c_aux_11 Post5 c_aux_12 Post3)) in
           (exist_1 [result0: Z]`result0 = 5` result Post9) in
         (exist_2 [x1: Z][result0: Z]`result0 = 5` x0 result Post8) in
       (exist_3 [x1: Z][y1: Z][result0: unit]`y1 = 5` x0 result tt Post4).

(* Why obligation from file "good-c/all.c", characters 1071-1074 *)
Lemma e4_po_1 : 
  (x: Z)
  (Pre1: `x = 2`)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  ((result:Z) (result = x0 -> `x0 + result = 6`)).
Proof.
Intuition.
Save.

(* Why obligation from file "good-c/all.c", characters 1071-1078 *)
Lemma e4_po_2 : 
  (x: Z)
  (Pre1: `x = 2`)
  (x0: Z)
  (c_aux_13: Z)
  (Post4: ((result:Z) (result = x0 -> `c_aux_13 + result = 6`)))
  (c_aux_14: Z)
  (Post2: c_aux_14 = x0)
  `c_aux_13 + c_aux_14 = 6`.
Proof.
Intuition.
Save.

Definition e4 (* validation *)
  : (_: unit)(x: Z)(y: Z)(_: `x = 2`)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`y0 = 6`))
  := [_: unit; x: Z; y: Z; Pre1: `x = 2`]
       let (x0, result, Post3) =
         let (x0, c_aux_13, Post4) =
           let (x0, result, Post1) =
             let (result, Post1) = (exist_1 [result: Z]
               result = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
             (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
           let (result0, Post5) = (exist_1 [result0: Z]
             ((result:Z) (result = x0 -> `result0 + result = 6`)) x0
             (e4_po_1 x Pre1 x0 Post1)) in
           (exist_2 [x1: Z][result1: Z]
           ((result:Z) (result = x1 -> `result1 + result = 6`)) x0 result0
           Post5) in
         let (result, Post6) =
           let (c_aux_14, Post2) = (exist_1 [result: Z]result = x0 x0
             (refl_equal ? x0)) in
           let (result, Post7) = (exist_1 [result: Z]
             `result = 6` `c_aux_13 + c_aux_14`
             (e4_po_2 x Pre1 x0 c_aux_13 Post4 c_aux_14 Post2)) in
           (exist_1 [result0: Z]`result0 = 6` result Post7) in
         (exist_2 [x1: Z][result0: Z]`result0 = 6` x0 result Post6) in
       (exist_3 [x1: Z][y1: Z][result0: unit]`y1 = 6` x0 result tt Post3).

(* Why obligation from file "good-c/all.c", characters 1125-1128 *)
Lemma e5_po_1 : 
  (x: Z)
  (Pre1: `x = 2`)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  ((result:Z) (result = x0 -> ((x:Z) (x = `x0 + 1` -> `x0 + result = 6`)))).
Proof.
Intuition.
Save.

(* Why obligation from file "good-c/all.c", characters 1131-1134 *)
Lemma e5_po_2 : 
  (x: Z)
  (Pre1: `x = 2`)
  (x0: Z)
  (c_aux_15: Z)
  (Post5: ((result:Z)
           (result = x0 -> ((x:Z) (x = `x0 + 1` -> `c_aux_15 + result = 6`)))))
  (c_aux_16: Z)
  (Post3: c_aux_16 = x0)
  (x1: Z)
  (Post2: x1 = `x0 + 1`)
  `c_aux_15 + c_aux_16 = 6`.
Proof.
Intuition.
Save.

Definition e5 (* validation *)
  : (_: unit)(x: Z)(y: Z)(_: `x = 2`)
    (sig_3 Z Z unit [x0: Z][y0: Z][result: unit](`y0 = 6`))
  := [_: unit; x: Z; y: Z; Pre1: `x = 2`]
       let (x0, result, Post4) =
         let (x0, c_aux_15, Post5) =
           let (x0, result, Post1) =
             let (result, Post1) = (exist_1 [result: Z]
               result = `x + 1` `x + 1` (refl_equal ? `x + 1`)) in
             (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
           let (result0, Post6) = (exist_1 [result0: Z]
             ((result:Z)
              (result = x0 ->
               ((x:Z) (x = `x0 + 1` -> `result0 + result = 6`)))) x0
             (e5_po_1 x Pre1 x0 Post1)) in
           (exist_2 [x1: Z][result1: Z]
           ((result:Z)
            (result = x1 -> ((x:Z) (x = `x1 + 1` -> `result1 + result = 6`)))) 
           x0 result0 Post6) in
         let (x1, result, Post7) =
           let (x1, c_aux_17, Post8) =
             let (c_aux_16, Post3) = (exist_1 [result: Z]result = x0 
               x0 (refl_equal ? x0)) in
             let (x1, result, Post9) =
               let (x1, result, Post2) =
                 let (result, Post2) = (exist_1 [result: Z]
                   result = `x0 + 1` `x0 + 1` (refl_equal ? `x0 + 1`)) in
                 (exist_2 [x2: Z][result0: unit]x2 = `x0 + 1` result 
                 tt Post2) in
               let (result0, Post10) = (exist_1 [result0: Z]
                 `c_aux_15 + result0 = 6` c_aux_16
                 (e5_po_2 x Pre1 x0 c_aux_15 Post5 c_aux_16 Post3 x1 Post2)) in
               (exist_2 [x2: Z][result1: Z]`c_aux_15 + result1 = 6` x1
               result0 Post10) in
             (exist_2 [x2: Z][result0: Z]`c_aux_15 + result0 = 6` x1 
             result Post9) in
           let (result, Post11) = (exist_1 [result: Z]
             `result = 6` `c_aux_15 + c_aux_17` Post8) in
           (exist_2 [x2: Z][result0: Z]`result0 = 6` x1 result Post11) in
         (exist_2 [x2: Z][result0: Z]`result0 = 6` x1 result Post7) in
       (exist_3 [x1: Z][y1: Z][result0: unit]`y1 = 6` x0 result tt Post4).

