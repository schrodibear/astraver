(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export struct2_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (Int_Z0: ((memory) Z Z0)),
  forall (alloc: alloc_table),
  forall (b_struct_S_7: ((memory) ((pointer) Z0) struct_S_7)),
  forall (s0: ((pointer) struct_S_7)),
  forall (u: ((pointer) struct_U_9)),
  forall (HW_1: (valid alloc u) /\ (valid alloc s0) /\
                (valid1 b_struct_S_7) /\ (valid1_range b_struct_S_7 5)),
  forall (result: ((pointer) Z0)),
  forall (HW_2: result = (acc b_struct_S_7 s0)),
  forall (result0: ((pointer) Z0)),
  forall (HW_3: result0 = (shift result 2)),
  forall (Int_Z0_0: ((memory) Z Z0)),
  forall (HW_4: Int_Z0_0 = (upd Int_Z0 result0 1)),
  (* File "struct2.c", line 6, characters 13-18 *) True.
Proof.
intuition.
Save.

Proof.
intuition.
subst.
unfold valid1_range in H2.
generalize (H2 s0 alloc HW_2).
intuition.
Save.


Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (Int_Z0: ((memory) Z Z0)),
  forall (alloc: alloc_table),
  forall (b_struct_S_3: ((memory) ((pointer) Z0) struct_S_3)),
  forall (d_struct_U_9: ((memory) ((pointer) struct_S_3) struct_U_9)),
  forall (s0: ((pointer) struct_S_7)),
  forall (u: ((pointer) struct_U_9)),
  forall (HW_1: (valid alloc u) /\ (valid alloc s0) /\
                (valid1 b_struct_S_3) /\ (valid1 d_struct_U_9) /\
                (separation2 d_struct_U_9 d_struct_U_9) /\
                (valid1_range b_struct_S_3 5)),
  forall (result: ((pointer) struct_S_3)),
  forall (HW_2: result = (acc d_struct_U_9 u)),
  forall (result0: ((pointer) Z0)),
  forall (HW_3: result0 = (acc b_struct_S_3 result)),
  forall (result1: ((pointer) Z0)),
  forall (HW_4: result1 = (shift result0 2)),
  forall (Int_Z0_0: ((memory) Z Z0)),
  forall (HW_5: Int_Z0_0 = (upd Int_Z0 result1 1)),
  (* File "struct2.c", line 16, characters 13-18 *) True.
Proof.
intuition.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst.
unfold valid1_range in H4.
Admitted.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

