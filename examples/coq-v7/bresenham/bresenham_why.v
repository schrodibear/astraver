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

(* Why obligation from file "bresenham.mlw", characters 1620-1630 *)
Lemma bresenham_po_1 : 
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

(* Why obligation from file "bresenham.mlw", characters 1656-1672 *)
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
  (Pre2: (best x1 y1))
  (Test3: `e1 < 0`)
  (e2: Z)
  (Post4: e2 = `e1 + 2 * y2`)
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

(* Why obligation from file "bresenham.mlw", characters 1684-1738 *)
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
  (Test2: `e1 >= 0`)
  (y3: Z)
  (Post5: y3 = `y1 + 1`)
  (e2: Z)
  (Post6: e2 = `e1 + 2 * (y2 - x2)`)
  ((x:Z)
   (x = `x1 + 1` -> ((`0 <= x` /\ `x <= x2 + 1`) /\ (invariant x y3 e2)) /\
    (Zwf `0` `x2 + 1 - x` `x2 + 1 - x1`))).
Proof.
Intros.
Subst x.
Unfold invariant. Unfold invariant in Pre3.
Split. Split. Omega'.
Split. 
Subst y3.
Replace `2*(x1+1+1)*y2-(2*(y1+1)+1)*x2` 
   with `2*(x1+1)*y2+2*y2-(2*y1+1)*x2-2*x2`;
 [ Omega' | Ring ].
Omega'.
Unfold Zwf; Omega'.
Save.

(* Why obligation from file "bresenham.mlw", characters 1493-1532 *)
Lemma bresenham_po_4 : 
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


