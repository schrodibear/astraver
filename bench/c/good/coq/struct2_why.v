(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export struct2_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (b_Z5: ((memory) ((pointer) Z0) Z5)),
  forall (s0: ((pointer) Z5)),
  forall (u: ((pointer) Z7)),
  forall (HW_1: (valid alloc u) /\ (valid alloc s0) /\ (valid1 b_Z5) /\
                (valid1_range b_Z5 5)),
  (valid alloc s0).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (b_Z5: ((memory) ((pointer) Z0) Z5)),
  forall (s0: ((pointer) Z5)),
  forall (u: ((pointer) Z7)),
  forall (HW_1: (valid alloc u) /\ (valid alloc s0) /\ (valid1 b_Z5) /\
                (valid1_range b_Z5 5)),
  forall (HW_2: (valid alloc s0)),
  forall (result: ((pointer) Z0)),
  forall (HW_3: result = (acc b_Z5 s0)),
  forall (result0: ((pointer) Z0)),
  forall (HW_4: result0 = (shift result 2)),
  (valid alloc result0).
Proof.
intuition.
subst.
unfold valid1_range in H2.
generalize (H2 s0 alloc HW_2).
intuition.
Save.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (b_Z5: ((memory) ((pointer) Z0) Z5)),
  forall (int_Z0: ((memory) Z Z0)),
  forall (s0: ((pointer) Z5)),
  forall (u: ((pointer) Z7)),
  forall (HW_1: (valid alloc u) /\ (valid alloc s0) /\ (valid1 b_Z5) /\
                (valid1_range b_Z5 5)),
  forall (HW_2: (valid alloc s0)),
  forall (result: ((pointer) Z0)),
  forall (HW_3: result = (acc b_Z5 s0)),
  forall (result0: ((pointer) Z0)),
  forall (HW_4: result0 = (shift result 2)),
  forall (HW_5: (valid alloc result0)),
  forall (int_Z0_0: ((memory) Z Z0)),
  forall (HW_6: int_Z0_0 = (upd int_Z0 result0 1)),
  (* File "struct2.c", line 6, characters 13-18 *) True.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (b_Z2: ((memory) ((pointer) Z0) Z2)),
  forall (d_Z7: ((memory) ((pointer) Z2) Z7)),
  forall (s0: ((pointer) Z5)),
  forall (u: ((pointer) Z7)),
  forall (HW_1: (valid alloc u) /\ (valid alloc s0) /\ (valid1 b_Z2) /\
                (valid1 d_Z7) /\ (separation2 d_Z7 d_Z7) /\
                (valid1_range b_Z2 5)),
  forall (HW_2: (valid alloc u)),
  forall (result: ((pointer) Z2)),
  forall (HW_3: result = (acc d_Z7 u)),
  (valid alloc result).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (b_Z2: ((memory) ((pointer) Z0) Z2)),
  forall (d_Z7: ((memory) ((pointer) Z2) Z7)),
  forall (s0: ((pointer) Z5)),
  forall (u: ((pointer) Z7)),
  forall (HW_1: (valid alloc u) /\ (valid alloc s0) /\ (valid1 b_Z2) /\
                (valid1 d_Z7) /\ (separation2 d_Z7 d_Z7) /\
                (valid1_range b_Z2 5)),
  forall (HW_2: (valid alloc u)),
  forall (result: ((pointer) Z2)),
  forall (HW_3: result = (acc d_Z7 u)),
  forall (HW_4: (valid alloc result)),
  forall (result0: ((pointer) Z0)),
  forall (HW_5: result0 = (acc b_Z2 result)),
  forall (result1: ((pointer) Z0)),
  forall (HW_6: result1 = (shift result0 2)),
  (valid alloc result1).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (b_Z2: ((memory) ((pointer) Z0) Z2)),
  forall (d_Z7: ((memory) ((pointer) Z2) Z7)),
  forall (int_Z0: ((memory) Z Z0)),
  forall (s0: ((pointer) Z5)),
  forall (u: ((pointer) Z7)),
  forall (HW_1: (valid alloc u) /\ (valid alloc s0) /\ (valid1 b_Z2) /\
                (valid1 d_Z7) /\ (separation2 d_Z7 d_Z7) /\
                (valid1_range b_Z2 5)),
  forall (HW_2: (valid alloc u)),
  forall (result: ((pointer) Z2)),
  forall (HW_3: result = (acc d_Z7 u)),
  forall (HW_4: (valid alloc result)),
  forall (result0: ((pointer) Z0)),
  forall (HW_5: result0 = (acc b_Z2 result)),
  forall (result1: ((pointer) Z0)),
  forall (HW_6: result1 = (shift result0 2)),
  forall (HW_7: (valid alloc result1)),
  forall (int_Z0_0: ((memory) Z Z0)),
  forall (HW_8: int_Z0_0 = (upd int_Z0 result1 1)),
  (* File "struct2.c", line 16, characters 13-18 *) True.
Proof.
intuition.
subst.
unfold valid1_range in H4.
Admitted.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

