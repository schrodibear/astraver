(**************************************************************************)
(*                                                                        *)
(* Proof of the Bresenham line drawing algorithm.                         *)
(*                                                                        *)
(* Jean-Christophe Filliâtre (LRI, Université Paris Sud)                  *)
(* May 2001                                                               *)
(*                                                                        *)
(**************************************************************************)

Require Import zaux.
Require Import Why.
Require Import ZArith.
 Require Import Omega.
Require Import ZArithRing.

(*Why*) Parameter x2 : Z.
(*Why*) Parameter y2 : Z.

Axiom first_octant : (0 <= y2 <= x2)%Z.

Ltac Omega' := generalize first_octant; omega.

(*s Specification of the correctness. 
    [(best x y)] expresses that the point [(x,y)] is the best
    possible point i.e. the closest to the real line. 
    This line has slope [y2/x2] thus the point on
    the line is [(x,x*y2/x2)]. *)

Definition best (x y:Z) :=
  forall y':Z, (Zabs (x2 * y - x * y2) <= Zabs (x2 * y' - x * y2))%Z.

(*s Invariant. The invariant relates [x], [y] and [e] and
    gives lower and upper bound for [e]. The key lemma 
    [invariant_is_ok] establishes that this invariant implies the
    expected property. *)

Definition invariant (x y e:Z) :=
  e = (2 * (x + 1) * y2 - (2 * y + 1) * x2)%Z /\
  (2 * (y2 - x2) <= e <= 2 * y2)%Z.

Lemma invariant_is_ok : forall x y e:Z, invariant x y e -> best x y.
Proof.
intros x y e.
unfold invariant; unfold best; intros [E I'] y'.
cut (0 <= x2)%Z; [ intro Hx2 | idtac ].
apply closest.
assumption.
apply (proj1 (Zabs_le (2 * x2 * y - 2 * (x * y2)) x2 Hx2)).
rewrite E in I'.
split.
(* 0 <= x2 *)
generalize (proj2 I').
RingSimpl (2 * (x + 1) * y2 - (2 * y + 1) * x2)%Z
 (2 * x * y2 - 2 * x2 * y + 2 * y2 - x2)%Z.
intro.
RingSimpl (2 * (x * y2))%Z (2 * x * y2)%Z.
omega.
(* 0 <= x2 *)
generalize (proj1 I').
RingSimpl (2 * (x + 1) * y2 - (2 * y + 1) * x2)%Z
 (2 * x * y2 - 2 * x2 * y + 2 * y2 - x2)%Z.
RingSimpl (2 * (y2 - x2))%Z (2 * y2 - 2 * x2)%Z.
RingSimpl (2 * (x * y2))%Z (2 * x * y2)%Z.
omega.
omega.
Qed.

(*s Program correctness. *)

(* Why obligation from file "bresenham.mlw", characters 1620-1630 *)
Lemma bresenham_po_1 : 
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (y0: Z),
  forall (Post2: y0 = 0),
  forall (e0: Z),
  forall (Post3: e0 = (2 * y2 - x2)),
  forall (Variant1: Z),
  forall (e1: Z),
  forall (x1: Z),
  forall (y1: Z),
  forall (Pre4: Variant1 = (x2 + 1 - x1)),
  forall (Pre3: (0 <= x1 /\ x1 <= (x2 + 1)) /\ (invariant x1 y1 e1)),
  forall (Test4: x1 <= x2),
  (best x1 y1).
Proof.
intros.
decompose [and] Pre3.
exact (invariant_is_ok x1 y1 e1 H0).
Qed.

(* Why obligation from file "bresenham.mlw", characters 1656-1672 *)
Lemma bresenham_po_2 : 
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (y0: Z),
  forall (Post2: y0 = 0),
  forall (e0: Z),
  forall (Post3: e0 = (2 * y2 - x2)),
  forall (Variant1: Z),
  forall (e1: Z),
  forall (x1: Z),
  forall (y1: Z),
  forall (Pre4: Variant1 = (x2 + 1 - x1)),
  forall (Pre3: (0 <= x1 /\ x1 <= (x2 + 1)) /\ (invariant x1 y1 e1)),
  forall (Test4: x1 <= x2),
  forall (Pre2: (best x1 y1)),
  forall (Test3: e1 < 0),
  forall (e2: Z),
  forall (Post4: e2 = (e1 + 2 * y2)),
  (forall (x:Z),
   (x = (x1 + 1) -> ((0 <= x /\ x <= (x2 + 1)) /\ (invariant x y1 e2)) /\
    (Zwf 0 (x2 + 1 - x) (x2 + 1 - x1)))).
Proof.
intros.
rewrite H; clear x H.
split.
 split.
 Omega'.
unfold invariant.
 unfold invariant in Pre3.
split.
replace (2 * (x1 + 1 + 1) * y2)%Z with (2 * (x1 + 1) * y2 + 2 * y2)%Z;
 [ Omega' | ring ].
Omega'.
unfold Zwf; Omega'.
Qed.

(* Why obligation from file "bresenham.mlw", characters 1684-1738 *)
Lemma bresenham_po_3 : 
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (y0: Z),
  forall (Post2: y0 = 0),
  forall (e0: Z),
  forall (Post3: e0 = (2 * y2 - x2)),
  forall (Variant1: Z),
  forall (e1: Z),
  forall (x1: Z),
  forall (y1: Z),
  forall (Pre4: Variant1 = (x2 + 1 - x1)),
  forall (Pre3: (0 <= x1 /\ x1 <= (x2 + 1)) /\ (invariant x1 y1 e1)),
  forall (Test4: x1 <= x2),
  forall (Pre2: (best x1 y1)),
  forall (Test2: e1 >= 0),
  forall (y3: Z),
  forall (Post5: y3 = (y1 + 1)),
  forall (e2: Z),
  forall (Post6: e2 = (e1 + 2 * (y2 - x2))),
  (forall (x:Z),
   (x = (x1 + 1) -> ((0 <= x /\ x <= (x2 + 1)) /\ (invariant x y3 e2)) /\
    (Zwf 0 (x2 + 1 - x) (x2 + 1 - x1)))).
Proof.
intros.
subst x.
unfold invariant.
 unfold invariant in Pre3.
split.
 split.
 Omega'.
split.
 subst y3.
replace (2 * (x1 + 1 + 1) * y2 - (2 * (y1 + 1) + 1) * x2)%Z with
 (2 * (x1 + 1) * y2 + 2 * y2 - (2 * y1 + 1) * x2 - 2 * x2)%Z;
 [ Omega' | ring ].
Omega'.
unfold Zwf; Omega'.
Qed.

(* Why obligation from file "bresenham.mlw", characters 1493-1532 *)
Lemma bresenham_po_4 : 
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (y0: Z),
  forall (Post2: y0 = 0),
  forall (e0: Z),
  forall (Post3: e0 = (2 * y2 - x2)),
  (0 <= x0 /\ x0 <= (x2 + 1)) /\ (invariant x0 y0 e0).
Proof.
intuition.
Omega'.
subst x0; subst y0; subst e0; unfold invariant; Omega'.
Qed.


