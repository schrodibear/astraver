(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export ref_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  1 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z3)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  (* File "ref.c", line 4, characters 14-23 *) (valid alloc0 result).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (int_Z3: ((memory) Z Z3)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z3)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (* File "ref.c", line 4, characters 14-23 *)
                (valid alloc0 result)),
  forall (int_Z3_0: ((memory) Z Z3)),
  forall (HW_4: (* File "ref.c", line 6, characters 13-20 *)
                (acc int_Z3_0 result) = 1 /\
                (not_assigns alloc0 int_Z3 int_Z3_0 (pset_singleton result))),
  (valid alloc0 result).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (int_Z3: ((memory) Z Z3)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z3)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (* File "ref.c", line 4, characters 14-23 *)
                (valid alloc0 result)),
  forall (int_Z3_0: ((memory) Z Z3)),
  forall (HW_4: (* File "ref.c", line 6, characters 13-20 *)
                (acc int_Z3_0 result) = 1 /\
                (not_assigns alloc0 int_Z3 int_Z3_0 (pset_singleton result))),
  forall (HW_5: (valid alloc0 result)),
  forall (result0: Z),
  forall (HW_6: result0 = (acc int_Z3_0 result)),
  (* File "ref.c", line 13, characters 13-25 *) result0 = 1 /\
  (not_assigns alloc int_Z3 int_Z3_0 pset_empty).
Proof.
intuition.
red;intros.
rewrite H7;auto.
apply alloc_stack_valid with Z3 result alloc;auto.
assert (p<> result).
intro;subst.
rewrite <- shift_zero in H8.
generalize H8.
apply fresh_not_valid;auto.
apply pset_singleton_intro;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (p: ((pointer) Z3)),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "ref.c", line 4, characters 14-23 *) (valid alloc p)),
  (valid alloc p).
Proof.
intuition; subst; caduceus.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (p: ((pointer) Z3)),
  forall (alloc: alloc_table),
  forall (int_Z3: ((memory) Z Z3)),
  forall (HW_1: (* File "ref.c", line 4, characters 14-23 *) (valid alloc p)),
  forall (HW_2: (valid alloc p)),
  forall (int_Z3_0: ((memory) Z Z3)),
  forall (HW_3: int_Z3_0 = (upd int_Z3 p 1)),
  (* File "ref.c", line 6, characters 13-20 *) (acc int_Z3_0 p) = 1 /\
  (not_assigns alloc int_Z3 int_Z3_0 (pset_singleton p)).
Proof.
intuition;subst;caduceus.
red;intros.
rewrite acc_upd_neq;auto.
assert (p0<>p).
apply pset_singleton_elim;auto.
auto.
Save.

