(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Omega.

Parameter q : Z -> Prop.

Lemma p1_po_1 : 
  (x: Z)
  (Pre1: (q `x + 1`))
  (x0: Z)
  (Post1: x0 = `x + 1`)
  (q x0).
Proof. 
Intros; Rewrite Post1; Assumption.
Save.


Definition p1 := (* validation *)
  [x: Z; Pre1: (q `x + 1`)]
    let (x0, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `x + 1` `x + 1`
        (refl_equal ? `x + 1`)) in
      (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
    (exist_2 [x1: Z][result0: unit](q x1) x0 result
    (p1_po_1 x Pre1 x0 Post1)).

Lemma p2_po_1 : 
  (Pre1: (q `7`))
  (x0: Z)
  (Post1: x0 = `3 + 4`)
  (q x0).
Proof.
Intros; Rewrite Post1; Assumption.
Save.


Definition p2 := (* validation *)
  [x: Z; Pre1: (q `7`)]
    let (x0, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `3 + 4` `3 + 4`
        (refl_equal ? `3 + 4`)) in
      (exist_2 [x1: Z][result0: unit]x1 = `3 + 4` result tt Post1) in
    (exist_2 [x1: Z][result0: unit](q x1) x0 result (p2_po_1 Pre1 x0 Post1)).

Lemma p3_po_1 : 
  (x: Z)
  (x0: Z)
  (Post1: x0 = `x + 1`)
  (x1: Z)
  (Post2: x1 = `x0 + 2`)
  `x1 = x + 3`.
Proof. 
Intros; Omega.
Save.


Definition p3 := (* validation *)
  [x: Z]
    let (x0, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `x + 1` `x + 1`
        (refl_equal ? `x + 1`)) in
      (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
    let (x1, result0, Post2) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = `x0 + 2` 
        `x0 + 2` (refl_equal ? `x0 + 2`)) in
      (exist_2 [x2: Z][result1: unit]x2 = `x0 + 2` result0 tt Post2) in
    (exist_2 [x2: Z][result1: unit]`x2 = x + 3` x1 result0
    (p3_po_1 x x0 Post1 x1 Post2)).

Lemma p4_po_1 : 
  (x0: Z)
  (Post1: x0 = `7`)
  (x1: Z)
  (Post2: x1 = `2 * x0`)
  `x1 = 14`.
Proof. 
Intros; Omega.
Save.


Definition p4 := (* validation *)
  [x: Z]
    let (x0, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `7` `7`
        (refl_equal ? `7`)) in
      (exist_2 [x1: Z][result0: unit]x1 = `7` result tt Post1) in
    let (x1, result0, Post2) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = `2 * x0` 
        `2 * x0` (refl_equal ? `2 * x0`)) in
      (exist_2 [x2: Z][result1: unit]x2 = `2 * x0` result0 tt Post2) in
    (exist_2 [x2: Z][result1: unit]`x2 = 14` x1 result0
    (p4_po_1 x0 Post1 x1 Post2)).

Lemma p5_po_1 : 
  `3 + 4 = 7`.
Proof.
Omega.
Save.


Definition p5 := (* validation *)
  (exist_1 [result: Z]`result = 7` `3 + 4` p5_po_1).

Lemma p6_po_1 : 
  (a: Z)
  (Post1: a = `3`)
  `a + 4 = 7`.
Proof.
Intros; Omega.
Save.


Definition p6 := (* validation *)
  let (a, Post1) = (exist_1 [result: Z]result = `3` `3`
    (refl_equal ? `3`)) in
  let (result, Post2) = (exist_1 [result: Z]`result = 7` `a + 4`
    (p6_po_1 a Post1)) in
  (exist_1 [result0: Z]`result0 = 7` result Post2).

Lemma p7_po_1 : 
  (a: Z)
  (Post1: a = `4`)
  `3 + (a + a) = 11`.
Proof.
Intros; Omega.
Save.


Definition p7 := (* validation *)
  let (aux_1, Post2) =
    let (a, Post1) = (exist_1 [result: Z]result = `4` `4`
      (refl_equal ? `4`)) in
    let (result, Post3) = (exist_1 [result: Z]`3 + result = 11` `a + a`
      (p7_po_1 a Post1)) in
    (exist_1 [result0: Z]`3 + result0 = 11` result Post3) in
  let (result, Post4) = (exist_1 [result: Z]`result = 11` `3 + aux_1`
    Post2) in
  (exist_1 [result0: Z]`result0 = 11` result Post4).

Lemma p8_po_1 : 
  (x: Z)
  (Pre1: (q `x + 1`))
  (x0: Z)
  (Post1: x0 = `x + 1`)
  (q x0) /\ `3 + x0 = x + 4`.
Proof.
Intuition; Rewrite Post1; Assumption.
Save.


Definition p8 := (* validation *)
  [x: Z; Pre1: (q `x + 1`)]
    let (x0, aux_1, Post2) =
      let (x0, result, Post1) =
        let (result, Post1) = (exist_1 [result: Z]result = `x + 1` `x + 1`
          (refl_equal ? `x + 1`)) in
        (exist_2 [x1: Z][result0: unit]x1 = `x + 1` result tt Post1) in
      let (result0, Post3) = (exist_1 [result0: Z](q x0) /\
        `3 + result0 = x + 4` x0 (p8_po_1 x Pre1 x0 Post1)) in
      (exist_2 [x1: Z][result1: Z](q x1) /\ `3 + result1 = x + 4` x0 
      result0 Post3) in
    let (result, Post4) = (exist_1 [result: Z](q x0) /\
      `result = x + 4` `3 + aux_1` Post2) in
    (exist_2 [x1: Z][result0: Z](q x1) /\ `result0 = x + 4` x0 result Post4).

Lemma p9_po_1 : 
  (x0: Z)
  (Post2: x0 = `2`)
  ((x:Z) (x = `1` -> `1 + 1 = 2` /\ `x = 1`)).
Proof.
Intuition.
Save.

Lemma p9_po_2 : 
  (aux_2: Z)
  (Post3: ((x:Z) (x = `1` -> `1 + aux_2 = 2` /\ `x = 1`)))
  (x1: Z)
  (Post1: x1 = `1`)
  `1 + aux_2 = 2` /\ `x1 = 1`.
Proof.
Intuition.
Save.


Definition p9 := (* validation *)
  [x: Z]
    let (x0, aux_2, Post3) =
      let (x0, result, Post2) =
        let (result, Post2) = (exist_1 [result: Z]result = `2` `2`
          (refl_equal ? `2`)) in
        (exist_2 [x1: Z][result0: unit]x1 = `2` result tt Post2) in
      let (result0, Post4) = (exist_1 [result0: Z]
        ((x:Z) (x = `1` -> `1 + result0 = 2` /\ `x = 1`)) `1`
        (p9_po_1 x0 Post2)) in
      (exist_2 [x1: Z][result1: Z]
      ((x:Z) (x = `1` -> `1 + result1 = 2` /\ `x = 1`)) x0 result0 Post4) in
    let (x1, result, Post5) =
      let (x1, aux_1, Post6) =
        let (x1, result, Post1) =
          let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
            (refl_equal ? `1`)) in
          (exist_2 [x2: Z][result0: unit]x2 = `1` result tt Post1) in
        let (result0, Post7) = (exist_1 [result0: Z]`result0 + aux_2 = 2` /\
          `x1 = 1` `1` (p9_po_2 aux_2 Post3 x1 Post1)) in
        (exist_2 [x2: Z][result1: Z]`result1 + aux_2 = 2` /\ `x2 = 1` 
        x1 result0 Post7) in
      let (result, Post8) = (exist_1 [result: Z]`result = 2` /\
        `x1 = 1` `aux_1 + aux_2` Post6) in
      (exist_2 [x2: Z][result0: Z]`result0 = 2` /\ `x2 = 1` x1 result Post8) in
    (exist_2 [x2: Z][result0: Z]`result0 = 2` /\ `x2 = 1` x1 result Post5).

Lemma p9a_po_1 : 
  (x0: Z)
  (Post1: x0 = `1`)
  `1 + 1 = 2` /\ `x0 = 1`.
Proof.
Intuition.
Save.


Definition p9a := (* validation *)
  [x: Z]
    let (x0, aux_1, Post2) =
      let (x0, result, Post1) =
        let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
          (refl_equal ? `1`)) in
        (exist_2 [x1: Z][result0: unit]x1 = `1` result tt Post1) in
      let (result0, Post3) = (exist_1 [result0: Z]`result0 + 1 = 2` /\
        `x0 = 1` `1` (p9a_po_1 x0 Post1)) in
      (exist_2 [x1: Z][result1: Z]`result1 + 1 = 2` /\ `x1 = 1` x0 result0
      Post3) in
    let (result, Post4) = (exist_1 [result: Z]`result = 2` /\
      `x0 = 1` `aux_1 + 1` Post2) in
    (exist_2 [x1: Z][result0: Z]`result0 = 2` /\ `x1 = 1` x0 result Post4).

(*Why*) Parameter fsucc : (x: Z)(sig_1 Z [result: Z](`result = x + 1`)).

Lemma p10_po_1 : 
  (result1: Z)
  (Post1: `result1 = 0 + 1`)
  `result1 = 1`.
Proof.
Intros; Omega.
Save.


Definition p10 := (* validation *)
  let (result1, Post1) = (fsucc `0`) in
  (exist_1 [result2: Z]`result2 = 1` result1 (p10_po_1 result1 Post1)).

Lemma p11_po_1 : 
  (aux_2: Z)
  (Post1: `aux_2 = 3 + 1`)
  (aux_1: Z)
  (Post4: `aux_1 = 0 + 1`)
  `aux_1 + aux_2 = 5`.
Proof.
Intros; Omega.
Save.


Definition p11 := (* validation *)
  let (aux_2, Post1) =
    let (result1, Post2) = (fsucc `3`) in
    (exist_1 [result2: Z]`result2 = 3 + 1` result1 Post2) in
  let (result, Post3) =
    let (aux_1, Post4) =
      let (result1, Post5) = (fsucc `0`) in
      (exist_1 [result2: Z]`result2 = 0 + 1` result1 Post5) in
    let (result, Post6) = (exist_1 [result: Z]`result = 5` `aux_1 + aux_2`
      (p11_po_1 aux_2 Post1 aux_1 Post4)) in
    (exist_1 [result0: Z]`result0 = 5` result Post6) in
  (exist_1 [result0: Z]`result0 = 5` result Post3).

Lemma p11a_po_1 : 
  (a: Z)
  (Post1: `a = 1 + 1`)
  `a + a = 4`.
Proof.
Intros; Omega.
Save.


Definition p11a := (* validation *)
  let (a, Post1) =
    let (result1, Post2) = (fsucc `1`) in
    (exist_1 [result2: Z]`result2 = 1 + 1` result1 Post2) in
  let (result, Post3) = (exist_1 [result: Z]`result = 4` `a + a`
    (p11a_po_1 a Post1)) in
  (exist_1 [result0: Z]`result0 = 4` result Post3).

(*Why*) Parameter incrx :
  (_: unit)(x: Z)(sig_2 Z unit [x0: Z][result: unit](`x0 = x + 1`)).

Lemma p12_po_1 : 
  (x: Z)
  (Pre1: `x = 0`)
  (x0: Z)
  (Post1: `x0 = x + 1`)
  `x0 = 1`.
Proof.
Intros; Omega.
Save.


Definition p12 := (* validation *)
  [x: Z; Pre1: `x = 0`]
    let (x0, result1, Post1) = (incrx tt x) in
    (exist_2 [x1: Z][result2: unit]`x1 = 1` x0 result1
    (p12_po_1 x Pre1 x0 Post1)).

Lemma p13_po_1 : 
  (x: Z)
  (x0: Z)
  (Post1: `x0 = x + 1`)
  (x1: Z)
  (Post3: `x1 = x0 + 1`)
  `x1 = x + 2`.
Proof.
Intros; Omega.
Save.


Definition p13 := (* validation *)
  [x: Z]
    let (x0, result, Post1) =
      let (x0, result1, Post2) = (incrx tt x) in
      (exist_2 [x1: Z][result2: unit]`x1 = x + 1` x0 result1 Post2) in
    let (x1, result0, Post3) =
      let (x1, result2, Post4) = (incrx tt x0) in
      (exist_2 [x2: Z][result3: unit]`x2 = x0 + 1` x1 result2 Post4) in
    (exist_2 [x2: Z][result1: unit]`x2 = x + 2` x1 result0
    (p13_po_1 x x0 Post1 x1 Post3)).

Lemma p13a_po_1 : 
  (x: Z)
  (x0: Z)
  (Post1: `x0 = x + 1`)
  (x1: Z)
  (Post3: `x1 = x0 + 1`)
  `x1 = x + 2`.
Proof.
Intros; Omega.
Save.


Definition p13a := (* validation *)
  [x: Z]
    let (x0, aux_1, Post1) =
      let (x0, result1, Post2) = (incrx tt x) in
      (exist_2 [x1: Z][result2: unit]`x1 = x + 1` x0 result1 Post2) in
    let (x1, result, Post3) =
      let (x1, result1, Post4) = (incrx aux_1 x0) in
      (exist_2 [x2: Z][result2: unit]`x2 = x0 + 1` x1 result1 Post4) in
    (exist_2 [x2: Z][result0: unit]`x2 = x + 2` x1 result
    (p13a_po_1 x x0 Post1 x1 Post3)).

(*Why*) Parameter incrx2 :
  (_: unit)(x: Z)
  (sig_2 Z Z [x0: Z][result: Z](`x0 = x + 1` /\ `result = x0`)).

Lemma p14_po_1 : 
  (x: Z)
  (Pre1: `x = 0`)
  (x0: Z)
  (result1: Z)
  (Post1: `x0 = x + 1` /\ `result1 = x0`)
  `result1 = 1`.
Proof.
Intros; Omega.
Save.


Definition p14 := (* validation *)
  [x: Z; Pre1: `x = 0`]
    let (x0, result1, Post1) = (incrx2 tt x) in
    (exist_2 [x1: Z][result2: Z]`result2 = 1` x0 result1
    (p14_po_1 x Pre1 x0 result1 Post1)).

Lemma p15_po_1 : 
  `0 <= 0` /\ `0 < 10`.
Proof. (* p15_po_1 *)
Omega.
Save.


Definition p15 := (* validation *)
  [t: (array `10` Z)]let Pre1 = p15_po_1 in
                     (access t `0`).

Lemma p16_po_1 : 
  (t: (array `10` Z))
  (result: Z)
  (Post1: (store t `9` result) = (store t `9` `1`))
  `0 <= 9` /\ `9 < 10`.
Proof. (* p16_po_1 *)
Intros; Omega.
Save.


Definition p16 := (* validation *)
  [t: (array `10` Z)]
    let (result, Post1) = (exist_1 [result: Z]
      (store t `9` result) = (store t `9` `1`) `1`
      (refl_equal ? (store t `9` `1`))) in
    let Pre1 = (p16_po_1 t result Post1) in
    (exist_2 [t1: (array `10` Z)][result1: unit]
    t1 = (store t `9` `1`) (store t `9` result) tt Post1).

Lemma p17_po_1 : 
  (t: (array `10` Z))
  (Pre3: `0 <= (access t 0)` /\ `(access t 0) < 10`)
  `0 <= 0` /\ `0 < 10`.
Proof. (* p17_po_1 *)
Intros; Omega.
Save.


(* 
 Local Variables:
 mode: coq 
  coq-prog-name: "coqtop -emacs -q -I ../../lib/coq"
 End:
*)

Definition p17 := (* validation *)
  [t: (array `10` Z); Pre3: `0 <= (access t 0)` /\ `(access t 0) < 10`]
    let Pre2 = (p17_po_1 t Pre3) in
    let (result, Post1) = (exist_1 [result: Z]
      (store t (access t `0`) result) = (store t (access t `0`) `1`) 
      `1` (refl_equal ? (store t (access t `0`) `1`))) in
    let Pre1 = Pre3 in
    (exist_2 [t1: (array `10` Z)][result1: unit]
    t1 = (store t (access t `0`) `1`) (store t (access t `0`) result) 
    tt Post1).

