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


Axiom first_octant : (0 <= y2 <= x2)%Z.

Ltac omega' := generalize first_octant; omega.

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

Definition Invariant (x y e:Z) :=
  e = (2 * (x + 1) * y2 - (2 * y + 1) * x2)%Z /\
  (2 * (y2 - x2) <= e <= 2 * y2)%Z.

Lemma invariant_is_ok : forall x y e:Z, Invariant x y e -> best x y.
Proof.
intros x y e.
unfold Invariant; unfold best; intros [E I'] y'.
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

(*Why logic*) Definition x2 : Z.
Admitted.

(*Why logic*) Definition y2 : Z.
Admitted.

Proof.
intuition.
omega'.
subst; unfold Invariant; omega'.
Save.

Proof.
intuition.
apply invariant_is_ok with e0; auto.
Save.

Proof.
unfold Invariant; intuition; subst.
replace (2 * (x0 + 1 + 1) * y2)%Z with (2 * (x0 + 1) * y2 + 2 * y2)%Z;
 [ omega' | ring ].
omega'.
Save.

Proof.
unfold Invariant; intuition; subst.
replace (2 * (x0 + 1 + 1) * y2 - (2 * (y0 + 1) + 1) * x2)%Z with
 (2 * (x0 + 1) * y2 + 2 * y2 - (2 * y0 + 1) * x2 - 2 * x2)%Z;
 [ omega' | ring ].
omega'.
Save.


(*Why axiom*) Lemma first_octant : 0 <= y2 /\ y2 <= x2.
Admitted.

(*Why logic*) Definition abs : Z -> Z.
Admitted.

(*Why axiom*) Lemma abs_def :
  (forall (x:Z), x >= 0 /\ (abs x) = x \/ x <= 0 /\ (abs x) = (Zopp x)).
Admitted.

(*Why predicate*) Definition best  (x:Z) (y:Z)
  := (forall (y':Z), (abs (x2 * y - x * y2)) <= (abs (x2 * y' - x * y2))).

(*Why predicate*) Definition Invariant  (x:Z) (y:Z) (e:Z)
  := e = (2 * (x + 1) * y2 - (2 * y + 1) * x2) /\ (2 * (y2 - x2)) <= e /\
     e <= (2 * y2).

(*Why axiom*) Lemma invariant_is_ok :
  (forall (x:Z),
   (forall (y:Z), (forall (e:Z), ((Invariant x y e) -> (best x y))))).
Admitted.

(* Why obligation from file "bresenham.mlw", line 52, characters 18-57: *)
(*Why goal*) Lemma bresenham_po_1 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  0 <= x.
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 52, characters 18-57: *)
(*Why goal*) Lemma bresenham_po_2 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  x <= (x2 + 1).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 52, characters 18-57: *)
(*Why goal*) Lemma bresenham_po_3 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  (Invariant x y e).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 55, characters 15-25: *)
(*Why goal*) Lemma bresenham_po_4 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  forall (e0: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_4: (0 <= x0 /\ x0 <= (x2 + 1)) /\ (Invariant x0 y0 e0)),
  forall (HW_5: x0 <= x2),
  (best x0 y0).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 52, characters 18-57: *)
(*Why goal*) Lemma bresenham_po_5 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  forall (e0: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_4: (0 <= x0 /\ x0 <= (x2 + 1)) /\ (Invariant x0 y0 e0)),
  forall (HW_5: x0 <= x2),
  forall (HW_6: (best x0 y0)),
  forall (HW_7: e0 < 0),
  forall (e1: Z),
  forall (HW_8: e1 = (e0 + 2 * y2)),
  forall (x1: Z),
  forall (HW_9: x1 = (x0 + 1)),
  0 <= x1.
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 52, characters 18-57: *)
(*Why goal*) Lemma bresenham_po_6 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  forall (e0: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_4: (0 <= x0 /\ x0 <= (x2 + 1)) /\ (Invariant x0 y0 e0)),
  forall (HW_5: x0 <= x2),
  forall (HW_6: (best x0 y0)),
  forall (HW_7: e0 < 0),
  forall (e1: Z),
  forall (HW_8: e1 = (e0 + 2 * y2)),
  forall (x1: Z),
  forall (HW_9: x1 = (x0 + 1)),
  x1 <= (x2 + 1).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 52, characters 18-57: *)
(*Why goal*) Lemma bresenham_po_7 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  forall (e0: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_4: (0 <= x0 /\ x0 <= (x2 + 1)) /\ (Invariant x0 y0 e0)),
  forall (HW_5: x0 <= x2),
  forall (HW_6: (best x0 y0)),
  forall (HW_7: e0 < 0),
  forall (e1: Z),
  forall (HW_8: e1 = (e0 + 2 * y2)),
  forall (x1: Z),
  forall (HW_9: x1 = (x0 + 1)),
  (Invariant x1 y0 e1).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 53, characters 18-28: *)
(*Why goal*) Lemma bresenham_po_8 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  forall (e0: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_4: (0 <= x0 /\ x0 <= (x2 + 1)) /\ (Invariant x0 y0 e0)),
  forall (HW_5: x0 <= x2),
  forall (HW_6: (best x0 y0)),
  forall (HW_7: e0 < 0),
  forall (e1: Z),
  forall (HW_8: e1 = (e0 + 2 * y2)),
  forall (x1: Z),
  forall (HW_9: x1 = (x0 + 1)),
  0 <= (x2 + 1 - x0).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 53, characters 18-28: *)
(*Why goal*) Lemma bresenham_po_9 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  forall (e0: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_4: (0 <= x0 /\ x0 <= (x2 + 1)) /\ (Invariant x0 y0 e0)),
  forall (HW_5: x0 <= x2),
  forall (HW_6: (best x0 y0)),
  forall (HW_7: e0 < 0),
  forall (e1: Z),
  forall (HW_8: e1 = (e0 + 2 * y2)),
  forall (x1: Z),
  forall (HW_9: x1 = (x0 + 1)),
  (x2 + 1 - x1) < (x2 + 1 - x0).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 52, characters 18-57: *)
(*Why goal*) Lemma bresenham_po_10 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  forall (e0: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_4: (0 <= x0 /\ x0 <= (x2 + 1)) /\ (Invariant x0 y0 e0)),
  forall (HW_5: x0 <= x2),
  forall (HW_6: (best x0 y0)),
  forall (HW_10: e0 >= 0),
  forall (y1: Z),
  forall (HW_11: y1 = (y0 + 1)),
  forall (e1: Z),
  forall (HW_12: e1 = (e0 + 2 * (y2 - x2))),
  forall (x1: Z),
  forall (HW_13: x1 = (x0 + 1)),
  0 <= x1.
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 52, characters 18-57: *)
(*Why goal*) Lemma bresenham_po_11 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  forall (e0: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_4: (0 <= x0 /\ x0 <= (x2 + 1)) /\ (Invariant x0 y0 e0)),
  forall (HW_5: x0 <= x2),
  forall (HW_6: (best x0 y0)),
  forall (HW_10: e0 >= 0),
  forall (y1: Z),
  forall (HW_11: y1 = (y0 + 1)),
  forall (e1: Z),
  forall (HW_12: e1 = (e0 + 2 * (y2 - x2))),
  forall (x1: Z),
  forall (HW_13: x1 = (x0 + 1)),
  x1 <= (x2 + 1).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 52, characters 18-57: *)
(*Why goal*) Lemma bresenham_po_12 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  forall (e0: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_4: (0 <= x0 /\ x0 <= (x2 + 1)) /\ (Invariant x0 y0 e0)),
  forall (HW_5: x0 <= x2),
  forall (HW_6: (best x0 y0)),
  forall (HW_10: e0 >= 0),
  forall (y1: Z),
  forall (HW_11: y1 = (y0 + 1)),
  forall (e1: Z),
  forall (HW_12: e1 = (e0 + 2 * (y2 - x2))),
  forall (x1: Z),
  forall (HW_13: x1 = (x0 + 1)),
  (Invariant x1 y1 e1).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 53, characters 18-28: *)
(*Why goal*) Lemma bresenham_po_13 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  forall (e0: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_4: (0 <= x0 /\ x0 <= (x2 + 1)) /\ (Invariant x0 y0 e0)),
  forall (HW_5: x0 <= x2),
  forall (HW_6: (best x0 y0)),
  forall (HW_10: e0 >= 0),
  forall (y1: Z),
  forall (HW_11: y1 = (y0 + 1)),
  forall (e1: Z),
  forall (HW_12: e1 = (e0 + 2 * (y2 - x2))),
  forall (x1: Z),
  forall (HW_13: x1 = (x0 + 1)),
  0 <= (x2 + 1 - x0).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "bresenham.mlw", line 53, characters 18-28: *)
(*Why goal*) Lemma bresenham_po_14 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y: Z),
  forall (HW_2: y = 0),
  forall (e: Z),
  forall (HW_3: e = (2 * y2 - x2)),
  forall (e0: Z),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_4: (0 <= x0 /\ x0 <= (x2 + 1)) /\ (Invariant x0 y0 e0)),
  forall (HW_5: x0 <= x2),
  forall (HW_6: (best x0 y0)),
  forall (HW_10: e0 >= 0),
  forall (y1: Z),
  forall (HW_11: y1 = (y0 + 1)),
  forall (e1: Z),
  forall (HW_12: e1 = (e0 + 2 * (y2 - x2))),
  forall (x1: Z),
  forall (HW_13: x1 = (x0 + 1)),
  (x2 + 1 - x1) < (x2 + 1 - x0).
Proof.
(* FILL PROOF HERE *)
Save.

(*Why*) Parameter bresenham_valid :
  forall (_: unit), forall (e: Z), forall (x: Z), forall (y: Z),
  (sig_4 Z Z Z unit (fun (e0: Z) (x0: Z) (y0: Z) (result: unit)  => (True))).

