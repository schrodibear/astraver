(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export modulo_spec_why.
Require Export Caduceus.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma math_mod_impl_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: (* File "modulo.c", line 2, characters 5-20 *) (x >= 0 /\ y >
                0)),
  (* File "modulo.c", line 8, characters 17-62 *) (0 <= x /\
  (exists d:Z, x = (d * y + x))).
Proof.
intuition; exists 0; intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma math_mod_impl_po_2 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: (* File "modulo.c", line 2, characters 5-20 *) (x >= 0 /\ y >
                0)),
  forall (HW_2: (* File "modulo.c", line 8, characters 17-62 *) (0 <= x /\
                (exists d:Z, x = (d * y + x)))),
  forall (mutable_x: Z),
  forall (HW_3: (* File "modulo.c", line 8, characters 17-62 *) (0 <=
                mutable_x /\ (exists d:Z, x = (d * y + mutable_x)))),
  forall (HW_4: mutable_x >= y),
  forall (mutable_x0: Z),
  forall (HW_5: mutable_x0 = (mutable_x - y)),
  (* File "modulo.c", line 8, characters 17-62 *) (0 <= mutable_x0 /\
  (exists d:Z, x = (d * y + mutable_x0))) /\ (Zwf 0 mutable_x0 mutable_x).
Proof.
intuition.
elim H4; intros d Hd; exists (d+1).
subst; ring.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma math_mod_impl_po_3 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: (* File "modulo.c", line 2, characters 5-20 *) (x >= 0 /\ y >
                0)),
  forall (HW_2: (* File "modulo.c", line 8, characters 17-62 *) (0 <= x /\
                (exists d:Z, x = (d * y + x)))),
  forall (mutable_x: Z),
  forall (HW_3: (* File "modulo.c", line 8, characters 17-62 *) (0 <=
                mutable_x /\ (exists d:Z, x = (d * y + mutable_x)))),
  forall (HW_6: mutable_x < y),
  (0 <= mutable_x /\ mutable_x < y) /\ (exists d:Z, x = (d * y + mutable_x)).
Proof.
intuition.
Save.

