(**************************************************************************)
(*                                                                        *)
(* Proof of the Bresenham line drawing algorithm.                         *)
(*                                                                        *)
(* Jean-Christophe Filliâtre (LRI, Université Paris Sud)                  *)
(* May 2001                                                               *)
(*                                                                        *)
(**************************************************************************)

Require zaux.
Require Why.
Require ZArith. 
Require Omega.
Require ZArithRing.

(*Why*) Parameter x2 : Z.
(*Why*) Parameter y2 : Z.

Axiom first_octant : `0 <= y2 <= x2`.

Tactic Definition Omega' := Generalize first_octant; Omega.

(*s Specification of the correctness. 
    [(best x y)] expresses that the point [(x,y)] is the best
    possible point i.e. the closest to the real line. 
    This line has slope [y2/x2] thus the point on
    the line is [(x,x*y2/x2)]. *)

Definition best := [x,y:Z](y':Z)`|x2*y-x*y2| <= |x2*y'-x*y2|`.

(*s Invariant. The invariant relates [x], [y] and [e] and
    gives lower and upper bound for [e]. The key lemma 
    [invariant_is_ok] establishes that this invariant implies the
    expected property. *)

Definition invariant := 
 [x,y,e:Z]`e = 2*(x+1)*y2 - (2*y+1)*x2` /\ `2*(y2-x2) <= e <= 2*y2`.

Lemma invariant_is_ok : 
  (x,y,e:Z)(invariant x y e) -> (best x y).
Proof.
Intros x y e.
Unfold invariant; Unfold best; Intros [E I'] y'.
Cut `0 <= x2`; [ Intro Hx2 | Idtac ].
Apply closest.
Assumption.
Apply (proj1 ? ? (Zabs_le `2*x2*y-2*(x*y2)` `x2` Hx2)).
Rewrite E in I'.
Split.
(* 0 <= x2 *)
Generalize (proj2 ? ? I').
RingSimpl '`2*(x+1)*y2-(2*y+1)*x2` '`2*x*y2-2*x2*y+2*y2-x2`.
Intro.
RingSimpl '`2*(x*y2)` '`2*x*y2`.
Omega.
(* 0 <= x2 *)
Generalize (proj1 ? ? I').
RingSimpl '`2*(x+1)*y2-(2*y+1)*x2` '`2*x*y2-2*x2*y+2*y2-x2`.
RingSimpl '`2*(y2-x2)` '`2*y2-2*x2`.
RingSimpl '`2*(x*y2)` '`2*x*y2`.
Omega.
Omega.
Save.

(*s Program correctness. *)

Lemma bresenham_po_1 : 
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `0`)
  (e0: Z)
  (Post3: e0 = `2 * y2 - x2`)
  (well_founded (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma bresenham_po_2 : 
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `0`)
  (e0: Z)
  (Post3: e0 = `2 * y2 - x2`)
  (Variant1: Z)
  (e1: Z)
  (x1: Z)
  (y1: Z)
  (Pre4: Variant1 = `x2 + 1 - x1`)
  (Pre3: (`0 <= x1` /\ `x1 <= x2 + 1`) /\ (invariant x1 y1 e1))
  (Test4: `x1 <= x2`)
  (best x1 y1).
Proof.
Intros.
Decompose [and] Pre3.
Exact (invariant_is_ok x1 y1 e1 H0).
Save.

Lemma bresenham_po_3 : 
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `0`)
  (e0: Z)
  (Post3: e0 = `2 * y2 - x2`)
  (Variant1: Z)
  (e1: Z)
  (x1: Z)
  (y1: Z)
  (Pre4: Variant1 = `x2 + 1 - x1`)
  (Pre3: (`0 <= x1` /\ `x1 <= x2 + 1`) /\ (invariant x1 y1 e1))
  (Test4: `x1 <= x2`)
  (Pre2: (best x1 y1))
  (Test3: `e1 < 0`)
  (e2: Z)
  (Post6: e2 = `e1 + 2 * y2`)
  ((x:Z)
   (x = `x1 + 1` -> ((`0 <= x` /\ `x <= x2 + 1`) /\ (invariant x y1 e2)) /\
    (Zwf `0` `x2 + 1 - x` `x2 + 1 - x1`))).
Proof.
Intros.
Rewrite H; Clear x H.
Split. Split. Omega'.
Unfold invariant. Unfold invariant in Pre3.
Split.
Replace `2*(x1+1+1)*y2` with `2*(x1+1)*y2+2*y2`;
 [ Omega' | Ring ].
Omega'.
Unfold Zwf; Omega'.
Save.

Lemma bresenham_po_4 : 
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `0`)
  (e0: Z)
  (Post3: e0 = `2 * y2 - x2`)
  (Variant1: Z)
  (e1: Z)
  (x1: Z)
  (y1: Z)
  (Pre4: Variant1 = `x2 + 1 - x1`)
  (Pre3: (`0 <= x1` /\ `x1 <= x2 + 1`) /\ (invariant x1 y1 e1))
  (Test4: `x1 <= x2`)
  (Pre2: (best x1 y1))
  (Test2: `e1 >= 0`)
  (y3: Z)
  (Post4: y3 = `y1 + 1`)
  (e2: Z)
  (Post5: e2 = `e1 + 2 * (y2 - x2)`)
  ((x:Z)
   (x = `x1 + 1` -> ((`0 <= x` /\ `x <= x2 + 1`) /\ (invariant x y3 e2)) /\
    (Zwf `0` `x2 + 1 - x` `x2 + 1 - x1`))).
Proof.
Intros.
Subst x.
Unfold invariant. Unfold invariant in Pre3.
Split. Split. Omega'.
Split. 
Rewrite Post4.
Replace `2*(x1+1+1)*y2-(2*(y1+1)+1)*x2` 
   with `2*(x1+1)*y2+2*y2-(2*y1+1)*x2-2*x2`;
 [ Omega' | Ring ].
Omega'.
Unfold Zwf; Omega'.
Save.

Lemma bresenham_po_5 : 
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `0`)
  (e0: Z)
  (Post3: e0 = `2 * y2 - x2`)
  (Variant1: Z)
  (e1: Z)
  (x1: Z)
  (y1: Z)
  (Pre4: Variant1 = `x2 + 1 - x1`)
  (Pre3: (`0 <= x1` /\ `x1 <= x2 + 1`) /\ (invariant x1 y1 e1))
  (Test4: `x1 <= x2`)
  (Pre2: (best x1 y1))
  (e2: Z)
  (y3: Z)
  (Post12: ((x:Z)
            (x = `x1 + 1` -> ((`0 <= x` /\ `x <= x2 + 1`) /\
             (invariant x y3 e2)) /\ (Zwf `0` `x2 + 1 - x` `x2 + 1 - x1`))))
  (x3: Z)
  (Post7: x3 = `x1 + 1`)
  ((`0 <= x3` /\ `x3 <= x2 + 1`) /\ (invariant x3 y3 e2)) /\
  (Zwf `0` `x2 + 1 - x3` `x2 + 1 - x1`).
Proof.
Intuition.
Save.

Lemma bresenham_po_6 : 
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `0`)
  (e0: Z)
  (Post3: e0 = `2 * y2 - x2`)
  (Variant1: Z)
  (e1: Z)
  (x1: Z)
  (y1: Z)
  (Pre4: Variant1 = `x2 + 1 - x1`)
  (Pre3: (`0 <= x1` /\ `x1 <= x2 + 1`) /\ (invariant x1 y1 e1))
  (Test4: `x1 <= x2`)
  (e2: Z)
  (x3: Z)
  (y3: Z)
  (Post9: ((`0 <= x3` /\ `x3 <= x2 + 1`) /\ (invariant x3 y3 e2)) /\
          (Zwf `0` `x2 + 1 - x3` `x2 + 1 - x1`))
  (Zwf `0` `x2 + 1 - x3` Variant1).
Proof.
Intros.
Rewrite Pre4; Tauto.
Save.

Lemma bresenham_po_7 : 
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `0`)
  (e0: Z)
  (Post3: e0 = `2 * y2 - x2`)
  (`0 <= x0` /\ `x0 <= x2 + 1`) /\ (invariant x0 y0 e0).
Proof.
Intuition.
Omega'.
Subst x0; Subst y0; Subst e0; Unfold invariant; Omega'.
Save.

Definition bresenham := (* validation *)
  [e: Z; x: Z; y: Z]
    let (x0, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `0` `0`
        (refl_equal ? `0`)) in
      (exist_2 [x1: Z][result0: unit]x1 = `0` result tt Post1) in
    let (y0, result0, Post2) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = `0` `0`
        (refl_equal ? `0`)) in
      (exist_2 [y1: Z][result1: unit]y1 = `0` result0 tt Post2) in
    let (e0, result1, Post3) =
      let (result1, Post3) = (exist_1 [result1: Z]
        result1 = `2 * y2 - x2` `2 * y2 - x2`
        (refl_equal ? `2 * y2 - x2`)) in
      (exist_2 [e1: Z][result2: unit]e1 = `2 * y2 - x2` result1 tt Post3) in
    let (e1, x1, y1, result2, Post8) =
      (well_founded_induction Z (Zwf ZERO)
        (bresenham_po_1 x0 Post1 y0 Post2 e0 Post3) [Variant1: Z](e1: Z)
        (x1: Z)(y1: Z)(_: Variant1 = `x2 + 1 - x1`)(_0: (`0 <= x1` /\
        `x1 <= x2 + 1`) /\ (invariant x1 y1 e1))
        (sig_4 Z Z Z unit [e2: Z][x3: Z][y3: Z][result2: unit](((`0 <= x3` /\
         `x3 <= x2 + 1`) /\ (invariant x3 y3 e2)) /\ `x3 > x2`))
        [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
         (e1: Z)(x1: Z)(y1: Z)(_: Variant2 = `x2 + 1 - x1`)(_0: (`0 <= x1` /\
         `x1 <= x2 + 1`) /\ (invariant x1 y1 e1))
         (sig_4 Z Z Z unit [e2: Z][x3: Z][y3: Z][result2: unit]
          (((`0 <= x3` /\ `x3 <= x2 + 1`) /\ (invariant x3 y3 e2)) /\
          `x3 > x2`));
         e1: Z; x1: Z; y1: Z; Pre4: Variant1 = `x2 + 1 - x1`;
         Pre3: (`0 <= x1` /\ `x1 <= x2 + 1`) /\ (invariant x1 y1 e1)]
          let (result2, Bool1) =
            let (result4, Post11) = (Z_le_gt_bool x1 x2) in
            (exist_1 [result5: bool]
            (if result5 then `x1 <= x2` else `x1 > x2`) result4 Post11) in
          (Cases (btest
                  [result2:bool](if result2 then `x1 <= x2` else `x1 > x2`)
                  result2 Bool1) of
          | (left Test4) =>
              let (e2, x3, y3, result3, Post8) =
                let (e2, x3, y3, result3, Post9) =
                  let Pre2 =
                    (bresenham_po_2 x0 Post1 y0 Post2 e0 Post3 Variant1 e1 x1
                    y1 Pre4 Pre3 Test4) in
                  let (e2, y3, result3, Post12) =
                    let (result3, Bool2) =
                      let (result5, Post13) = (Z_lt_ge_bool e1 `0`) in
                      (exist_1 [result6: bool]
                      (if result6 then `e1 < 0` else `e1 >= 0`) result5
                      Post13) in
                    (Cases (btest
                            [result3:bool](if result3 then `e1 < 0`
                                           else `e1 >= 0`)
                            result3 Bool2) of
                    | (left Test3) =>
                        let (e2, result4, Post6) =
                          let (result4, Post6) = (exist_1 [result4: Z]
                            result4 = `e1 + 2 * y2` `e1 + 2 * y2`
                            (refl_equal ? `e1 + 2 * y2`)) in
                          (exist_2 [e3: Z][result5: unit]
                          e3 = `e1 + 2 * y2` result4 tt Post6) in
                        (exist_3 [e3: Z][y3: Z][result5: unit]
                        ((x:Z)
                         (x = `x1 + 1` -> ((`0 <= x` /\ `x <= x2 + 1`) /\
                          (invariant x y3 e3)) /\
                          (Zwf `0` `x2 + 1 - x` `x2 + 1 - x1`))) e2
                        y1 result4
                        (bresenham_po_3 x0 Post1 y0 Post2 e0 Post3 Variant1
                        e1 x1 y1 Pre4 Pre3 Test4 Pre2 Test3 e2 Post6))
                    | (right Test2) =>
                        let (e2, y3, result4, Post14) =
                          let (y3, result4, Post4) =
                            let (result4, Post4) = (exist_1 [result4: Z]
                              result4 = `y1 + 1` `y1 + 1`
                              (refl_equal ? `y1 + 1`)) in
                            (exist_2 [y4: Z][result5: unit]
                            y4 = `y1 + 1` result4 tt Post4) in
                          let (e2, result5, Post5) =
                            let (result5, Post5) = (exist_1 [result5: Z]
                              result5 = `e1 + 2 * (y2 - x2)` `e1 + 2 *
                                                              (y2 - x2)`
                              (refl_equal ? `e1 + 2 * (y2 - x2)`)) in
                            (exist_2 [e3: Z][result6: unit]
                            e3 = `e1 + 2 * (y2 - x2)` result5 tt Post5) in
                          (exist_3 [e3: Z][y4: Z][result6: unit]
                          ((x:Z)
                           (x = `x1 + 1` -> ((`0 <= x` /\ `x <= x2 + 1`) /\
                            (invariant x y4 e3)) /\
                            (Zwf `0` `x2 + 1 - x` `x2 + 1 - x1`))) e2
                          y3 result5
                          (bresenham_po_4 x0 Post1 y0 Post2 e0 Post3 Variant1
                          e1 x1 y1 Pre4 Pre3 Test4 Pre2 Test2 y3 Post4 e2
                          Post5)) in
                        (exist_3 [e3: Z][y4: Z][result5: unit]
                        ((x:Z)
                         (x = `x1 + 1` -> ((`0 <= x` /\ `x <= x2 + 1`) /\
                          (invariant x y4 e3)) /\
                          (Zwf `0` `x2 + 1 - x` `x2 + 1 - x1`))) e2
                        y3 result4 Post14) end) in
                  let (x3, result4, Post7) =
                    let (result4, Post7) = (exist_1 [result4: Z]
                      result4 = `x1 + 1` `x1 + 1` (refl_equal ? `x1 + 1`)) in
                    (exist_2 [x4: Z][result5: unit]x4 = `x1 + 1` result4 
                    tt Post7) in
                  (exist_4 [e3: Z][x4: Z][y4: Z][result5: unit]((`0 <= x4` /\
                  `x4 <= x2 + 1`) /\ (invariant x4 y4 e3)) /\
                  (Zwf `0` `x2 + 1 - x4` `x2 + 1 - x1`) e2 x3 y3 result4
                  (bresenham_po_5 x0 Post1 y0 Post2 e0 Post3 Variant1 e1 x1
                  y1 Pre4 Pre3 Test4 Pre2 e2 y3 Post12 x3 Post7)) in
                ((wf1 `x2 + 1 - x3`)
                  (bresenham_po_6 x0 Post1 y0 Post2 e0 Post3 Variant1 e1 x1
                  y1 Pre4 Pre3 Test4 e2 x3 y3 Post9) e2 x3 y3
                  (refl_equal ? `x2 + 1 - x3`) (proj1 ? ? Post9)) in
              (exist_4 [e3: Z][x4: Z][y4: Z][result4: unit]((`0 <= x4` /\
              `x4 <= x2 + 1`) /\ (invariant x4 y4 e3)) /\ `x4 > x2` e2 
              x3 y3 result3 Post8)
          | (right Test1) =>
              let (e2, x3, y3, result3, Post8) = (exist_4 [e2: Z][x3: Z]
                [y3: Z][result3: unit]((`0 <= x3` /\ `x3 <= x2 + 1`) /\
                (invariant x3 y3 e2)) /\ `x3 > x2` e1 x1 y1 tt
                (conj ? ? Pre3 Test1)) in
              (exist_4 [e3: Z][x4: Z][y4: Z][result4: unit]((`0 <= x4` /\
              `x4 <= x2 + 1`) /\ (invariant x4 y4 e3)) /\ `x4 > x2` e2 
              x3 y3 result3 Post8) end) `x2 + 1 - x0` e0 x0 y0
        (refl_equal ? `x2 + 1 - x0`)
        (bresenham_po_7 x0 Post1 y0 Post2 e0 Post3)) in
    (Build_tuple_4 e1 x1 y1 result2).

