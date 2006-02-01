(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export ghost_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (t: ((pointer) Z1)),
  forall (u: ((pointer) Z4)),
  forall (x: Z),
  forall (HW_1: (valid_range alloc u 0 4) /\ (valid_range alloc t 0 9)),
  forall (pre_x: Z),
  forall (HW_2: pre_x = x),
  forall (x0: Z),
  forall (HW_3: x0 = (x + 1)),
  (* File "ghost.c", line 7, characters 13-29 *) pre_x = x.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (int_Z1: ((memory) Z Z1)),
  forall (int_Z4: ((memory) Z Z4)),
  forall (t: ((pointer) Z1)),
  forall (u: ((pointer) Z4)),
  forall (HW_1: (valid_range alloc u 0 4) /\ (valid_range alloc t 0 9)),
  forall (result: ((pointer) Z4)),
  forall (HW_2: result = (shift u 1)),
  forall (int_Z4_0: ((memory) Z Z4)),
  forall (HW_3: int_Z4_0 = (upd int_Z4 result 3)),
  forall (result0: ((pointer) Z4)),
  forall (HW_4: result0 = (shift u 1)),
  forall (result1: Z),
  forall (HW_5: result1 = (acc int_Z4_0 result0)),
  forall (int_Z1_0: ((memory) Z Z1)),
  forall (HW_6: int_Z1_0 = (upd int_Z1 t result1)),
  (* File "ghost.c", line 19, characters 13-44 *) ((acc int_Z4_0 u) =
  (acc int_Z4 u) /\ (acc int_Z1_0 t) = 3).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

