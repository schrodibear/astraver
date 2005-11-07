(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export coord_spec_why.

(* Why obligation from file "why/coord.why", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (index: Z),
  forall (alloc: alloc_table),
  forall (tab: ((pointer) Z2)),
  forall (x_Z2: ((memory) Z Z2)),
  forall (HW_1: (* File \"coord.c\", line 11, characters 14-28:\n *) (0 <=
                index /\ index < 3) /\ (valid_range alloc tab 0 2)),
  forall (result: ((pointer) Z2)),
  forall (HW_2: result = (shift tab index)),
  forall (result0: Z),
  forall (HW_3: result0 = (acc x_Z2 result)),
  forall (result1: ((pointer) Z2)),
  forall (HW_5: result1 = (shift tab index)),
  (valid alloc result1).
Proof.
intros.
intuition.
Save.
(* Why obligation from file "why/coord.why", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (index: Z),
  forall (alloc: alloc_table),
  forall (tab: ((pointer) Z2)),
  forall (HW_1: (* File \"coord.c\", line 11, characters 14-28:\n *) (0 <=
                index /\ index < 3) /\ (valid_range alloc tab 0 2)),
  forall (result: ((pointer) Z2)),
  forall (HW_2: result = (shift tab index)),
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

