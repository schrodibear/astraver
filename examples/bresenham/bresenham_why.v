(* Load Programs. *)(**************************************************************************)
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

(* Why obligation from file , characters 1620-1630 *)
Lemma bresenham_po_1 :
 forall (x0:Z) (Post1:x0 = 0%Z) (y0:Z) (Post2:y0 = 0%Z) (e0:Z)
   (Post3:e0 = (2 * y2 - x2)%Z) (Variant1 e1 x1 y1:Z)
   (Pre4:Variant1 = (x2 + 1 - x1)%Z)
   (Pre3:((0 <= x1)%Z /\ (x1 <= x2 + 1)%Z) /\ invariant x1 y1 e1)
   (Test4:(x1 <= x2)%Z), best x1 y1.
Proof.
intros.
decompose [and] Pre3.
exact (invariant_is_ok x1 y1 e1 H0).
Qed.

(* Why obligation from file , characters 1656-1672 *)
Lemma bresenham_po_2 :
 forall (x0:Z) (Post1:x0 = 0%Z) (y0:Z) (Post2:y0 = 0%Z) (e0:Z)
   (Post3:e0 = (2 * y2 - x2)%Z) (Variant1 e1 x1 y1:Z)
   (Pre4:Variant1 = (x2 + 1 - x1)%Z)
   (Pre3:((0 <= x1)%Z /\ (x1 <= x2 + 1)%Z) /\ invariant x1 y1 e1)
   (Test4:(x1 <= x2)%Z) (Pre2:best x1 y1) (Test3:(e1 < 0)%Z) (e2:Z)
   (Post4:e2 = (e1 + 2 * y2)%Z) (x:Z),
   x = (x1 + 1)%Z ->
   (((0 <= x)%Z /\ (x <= x2 + 1)%Z) /\ invariant x y1 e2) /\
   Zwf 0 (x2 + 1 - x) (x2 + 1 - x1).
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

(* Why obligation from file , characters 1684-1738 *)
Lemma bresenham_po_3 :
 forall (x0:Z) (Post1:x0 = 0%Z) (y0:Z) (Post2:y0 = 0%Z) (e0:Z)
   (Post3:e0 = (2 * y2 - x2)%Z) (Variant1 e1 x1 y1:Z)
   (Pre4:Variant1 = (x2 + 1 - x1)%Z)
   (Pre3:((0 <= x1)%Z /\ (x1 <= x2 + 1)%Z) /\ invariant x1 y1 e1)
   (Test4:(x1 <= x2)%Z) (Pre2:best x1 y1) (Test2:(e1 >= 0)%Z) (y3:Z)
   (Post5:y3 = (y1 + 1)%Z) (e2:Z) (Post6:e2 = (e1 + 2 * (y2 - x2))%Z)
   (x:Z),
   x = (x1 + 1)%Z ->
   (((0 <= x)%Z /\ (x <= x2 + 1)%Z) /\ invariant x y3 e2) /\
   Zwf 0 (x2 + 1 - x) (x2 + 1 - x1).
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

(* Why obligation from file , characters 1493-1532 *)
Lemma bresenham_po_4 :
 forall (x0:Z) (Post1:x0 = 0%Z) (y0:Z) (Post2:y0 = 0%Z) (e0:Z)
   (Post3:e0 = (2 * y2 - x2)%Z),
   ((0 <= x0)%Z /\ (x0 <= x2 + 1)%Z) /\ invariant x0 y0 e0.
Proof.
intuition.
Omega'.
subst x0; subst y0; subst e0; unfold invariant; Omega'.
Qed.


