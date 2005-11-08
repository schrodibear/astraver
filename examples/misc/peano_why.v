
Require Import Why.
Require Import Omega.
Require Import ZArithRing.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma add1_po_1 : 
  forall (y: Z),
  forall (x: Z),
  forall (HW_1: y >= 0),
  0 <= y /\ x = (x + (y - y)).
 Proof.
 unfold Zwf; intros; omega.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma add1_po_2 : 
  forall (y: Z),
  forall (x: Z),
  forall (HW_1: y >= 0),
  forall (HW_2: 0 <= y /\ x = (x + (y - y))),
  forall (x0: Z),
  forall (z: Z),
  forall (HW_3: 0 <= z /\ x0 = (x + (y - z))),
  forall (HW_4: z > 0),
  forall (x1: Z),
  forall (HW_5: x1 = (x0 + 1)),
  forall (z0: Z),
  forall (HW_6: z0 = (z - 1)),
  (0 <= z0 /\ x1 = (x + (y - z0))) /\ (Zwf 0 z0 z).
Proof.
unfold Zwf; intros; omega.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma add1_po_3 : 
  forall (y: Z),
  forall (x: Z),
  forall (HW_1: y >= 0),
  forall (HW_2: 0 <= y /\ x = (x + (y - y))),
  forall (x0: Z),
  forall (z: Z),
  forall (HW_3: 0 <= z /\ x0 = (x + (y - z))),
  forall (HW_7: z <= 0),
  x0 = (x + y).
Proof.
intuition.
Qed.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma u1_po_1 : 
  forall (r: Z),
  forall (HW_1: r = (3 + 7)),
  r = 10.
 Proof.
 intros; omega.
 Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma u1_po_2 : 
  forall (HW_2: (forall (r:Z), (r = (3 + 7) -> r = 10))),
  7 >= 0.
 Proof.
 intros; omega.
 Qed.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma rec_add1_po_1 : 
  forall (y: Z),
  forall (x: Z),
  forall (HW_1: y >= 0),
  forall (HW_2: 0 < y),
  forall (x0: Z),
  forall (HW_3: x0 = (x + 1)),
  forall (x1: Z),
  forall (HW_4: x1 = (x0 + (y - 1))),
  x1 = (x + y).
Proof.
intros; omega.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma rec_add1_po_2 : 
  forall (y: Z),
  forall (x: Z),
  forall (HW_1: y >= 0),
  forall (HW_2: 0 < y),
  forall (x0: Z),
  forall (HW_3: x0 = (x + 1)),
  forall (HW_5: (forall (x1:Z), (x1 = (x0 + (y - 1)) -> x1 = (x + y)))),
  (Zwf 0 (y - 1) y).
Proof.
intros; unfold Zwf; omega.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma rec_add1_po_3 : 
  forall (y: Z),
  forall (x: Z),
  forall (HW_1: y >= 0),
  forall (HW_2: 0 < y),
  forall (x0: Z),
  forall (HW_3: x0 = (x + 1)),
  forall (HW_6: (forall (x1:Z), (x1 = (x0 + (y - 1)) -> x1 = (x + y))) /\
                (Zwf 0 (y - 1) y)),
  (y - 1) >= 0.
Proof.
intros; omega.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma rec_add1_po_4 : 
  forall (y: Z),
  forall (x: Z),
  forall (HW_1: y >= 0),
  forall (HW_7: 0 >= y),
  x = (x + y).
Proof.
intros; omega.
Qed.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma u11_po_1 : 
  forall (r: Z),
  forall (HW_1: r = (3 + 7)),
  r = 10.
Proof.
intros; omega.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma u11_po_2 : 
  forall (HW_2: (forall (r:Z), (r = (3 + 7) -> r = 10))),
  7 >= 0.
Proof.
intros; omega.
Qed.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult1_po_1 : 
  forall (y: Z),
  forall (x: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  forall (x0: Z),
  forall (HW_2: x0 = 0),
  (* I *) (0 <= y /\ x0 = (x * (y - y))).
Proof.
intuition; ring; auto.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult1_po_2 : 
  forall (y: Z),
  forall (x: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  forall (x0: Z),
  forall (HW_2: x0 = 0),
  forall (HW_3: (* I *) (0 <= y /\ x0 = (x * (y - y)))),
  forall (x1: Z),
  forall (z: Z),
  forall (HW_4: (* I *) (0 <= z /\ x1 = (x * (y - z)))),
  forall (HW_5: z > 0),
  forall (x2: Z),
  forall (HW_6: x2 = (x1 + x)),
  forall (z0: Z),
  forall (HW_7: z0 = (z - 1)),
  (* I *) (0 <= z0 /\ x2 = (x * (y - z0))) /\ (Zwf 0 z0 z).
Proof.
simpl; intros.
repeat split; unfold Zwf; try omega.
subst x2 z0.
intuition.
subst.
ring.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult1_po_3 : 
  forall (y: Z),
  forall (x: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  forall (x0: Z),
  forall (HW_2: x0 = 0),
  forall (HW_3: (* I *) (0 <= y /\ x0 = (x * (y - y)))),
  forall (x1: Z),
  forall (z: Z),
  forall (HW_4: (* I *) (0 <= z /\ x1 = (x * (y - z)))),
  forall (HW_9: z <= 0),
  x1 = (x * y).
Proof.
simpl; intros.
assert (z = 0%Z). omega.
intuition; subst.
ring.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma u2_po_1 : 
  forall (r: Z),
  forall (HW_1: r = (4 * 6)),
  r = 24.
Proof.
 intros; omega.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma u2_po_2 : 
  forall (HW_2: (forall (r:Z), (r = (4 * 6) -> r = 24))),
  4 >= 0 /\ 6 >= 0.
Proof.
 intros; omega.
Qed.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult2_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  forall (a: Z),
  forall (b: Z),
  forall (HW_2: a >= 0),
  forall (HW_3: a = 0),
  b = (a + b).
Proof.
intros; subst; intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult2_po_2 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  forall (a: Z),
  forall (b: Z),
  forall (HW_2: a >= 0),
  forall (HW_4: a <> 0),
  forall (result: Z),
  forall (HW_5: result = (a - 1 + (b + 1))),
  result = (a + b).
Proof.
intuition; subst; ring.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult2_po_3 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  forall (a: Z),
  forall (b: Z),
  forall (HW_2: a >= 0),
  forall (HW_4: a <> 0),
  forall (HW_6: (forall (result:Z),
                 (result = (a - 1 + (b + 1)) -> result = (a + b)))),
  (Zwf 0 (a - 1) a).
Proof.
unfold Zwf; intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult2_po_4 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  forall (a: Z),
  forall (b: Z),
  forall (HW_2: a >= 0),
  forall (HW_4: a <> 0),
  forall (HW_7: (forall (result:Z),
                 (result = (a - 1 + (b + 1)) -> result = (a + b))) /\
                (Zwf 0 (a - 1) a)),
  (a - 1) >= 0.
Proof.
intuition.
Save.

