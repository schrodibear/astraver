(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export clash_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f1_impl_po_1 : 
  forall (ma_structure: ((pointer) Z6)),
  forall (alloc: alloc_table),
  forall (HW_1: (valid alloc ma_structure)),
  forall (toto_0: Z),
  forall (HW_3: toto_0 = 0),
  (valid alloc ma_structure).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f1_impl_po_2 : 
  forall (ma_structure: ((pointer) Z6)),
  forall (alloc: alloc_table),
  forall (toto_Z6: ((memory) Z Z6)),
  forall (HW_1: (valid alloc ma_structure)),
  forall (toto_0: Z),
  forall (HW_3: toto_0 = 0),
  forall (HW_4: (valid alloc ma_structure)),
  forall (toto_Z6_0: ((memory) Z Z6)),
  forall (HW_5: toto_Z6_0 = (upd toto_Z6 ma_structure toto_0)),
  (not_assigns alloc toto_Z6 toto_Z6_0 (pset_singleton ma_structure)).
Proof.
intuition.
subst.
red;intros.
rewrite acc_upd_neq;auto.
assert (p<> ma_structure).
apply pset_singleton_elim;auto.
auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_1 : 
  forall (ma_structure: ((pointer) Z7)),
  forall (alloc: alloc_table),
  forall (substruct_Z7: ((memory) ((pointer) Z2) Z7)),
  forall (HW_1: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                (valid alloc (acc substruct_Z7 ma_structure))) /\
                (valid1 substruct_Z7) /\
                (separation2 substruct_Z7 substruct_Z7)),
  1 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_2 : 
  forall (ma_structure: ((pointer) Z7)),
  forall (alloc: alloc_table),
  forall (substruct_Z7: ((memory) ((pointer) Z2) Z7)),
  forall (HW_1: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                (valid alloc (acc substruct_Z7 ma_structure))) /\
                (valid1 substruct_Z7) /\
                (separation2 substruct_Z7 substruct_Z7)),
  forall (HW_2: 1 >= 1),
  forall (result: ((pointer) Z8)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  (valid alloc0 result).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_3 : 
  forall (ma_structure: ((pointer) Z7)),
  forall (alloc: alloc_table),
  forall (fst_Z8: ((memory) Z Z8)),
  forall (substruct_Z7: ((memory) ((pointer) Z2) Z7)),
  forall (HW_1: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                (valid alloc (acc substruct_Z7 ma_structure))) /\
                (valid1 substruct_Z7) /\
                (separation2 substruct_Z7 substruct_Z7)),
  forall (HW_2: 1 >= 1),
  forall (result: ((pointer) Z8)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_4: (valid alloc0 result)),
  forall (fst_Z8_0: ((memory) Z Z8)),
  forall (HW_5: fst_Z8_0 = (upd fst_Z8 result 0)),
  (valid alloc0 ma_structure).
Proof.
intuition.
subst.
apply alloc_stack_valid with Z8 result alloc; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_4 : 
  forall (ma_structure: ((pointer) Z7)),
  forall (alloc: alloc_table),
  forall (fst_Z8: ((memory) Z Z8)),
  forall (substruct_Z7: ((memory) ((pointer) Z2) Z7)),
  forall (HW_1: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                (valid alloc (acc substruct_Z7 ma_structure))) /\
                (valid1 substruct_Z7) /\
                (separation2 substruct_Z7 substruct_Z7)),
  forall (HW_2: 1 >= 1),
  forall (result: ((pointer) Z8)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_4: (valid alloc0 result)),
  forall (fst_Z8_0: ((memory) Z Z8)),
  forall (HW_5: fst_Z8_0 = (upd fst_Z8 result 0)),
  forall (HW_6: (valid alloc0 ma_structure)),
  forall (result0: ((pointer) Z2)),
  forall (HW_7: result0 = (acc substruct_Z7 ma_structure)),
  (valid alloc0 result).
Proof.
intros.
subst;auto.
Save.



(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_5 : 
  forall (ma_structure: ((pointer) Z7)),
  forall (alloc: alloc_table),
  forall (fst_Z8: ((memory) Z Z8)),
  forall (substruct_Z7: ((memory) ((pointer) Z2) Z7)),
  forall (HW_1: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                (valid alloc (acc substruct_Z7 ma_structure))) /\
                (valid1 substruct_Z7) /\
                (separation2 substruct_Z7 substruct_Z7)),
  forall (HW_2: 1 >= 1),
  forall (result: ((pointer) Z8)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_4: (valid alloc0 result)),
  forall (fst_Z8_0: ((memory) Z Z8)),
  forall (HW_5: fst_Z8_0 = (upd fst_Z8 result 0)),
  forall (HW_6: (valid alloc0 ma_structure)),
  forall (result0: ((pointer) Z2)),
  forall (HW_7: result0 = (acc substruct_Z7 ma_structure)),
  forall (HW_8: (valid alloc0 result)),
  forall (result1: Z),
  forall (HW_9: result1 = (acc fst_Z8_0 result)),
  (valid alloc0 result0).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_6 : 
  forall (ma_structure: ((pointer) Z7)),
  forall (alloc: alloc_table),
  forall (fst_Z2: ((memory) Z Z2)),
  forall (fst_Z8: ((memory) Z Z8)),
  forall (substruct_Z7: ((memory) ((pointer) Z2) Z7)),
  forall (HW_1: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                (valid alloc (acc substruct_Z7 ma_structure))) /\
                (valid1 substruct_Z7) /\
                (separation2 substruct_Z7 substruct_Z7)),
  forall (HW_2: 1 >= 1),
  forall (result: ((pointer) Z8)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_4: (valid alloc0 result)),
  forall (fst_Z8_0: ((memory) Z Z8)),
  forall (HW_5: fst_Z8_0 = (upd fst_Z8 result 0)),
  forall (HW_6: (valid alloc0 ma_structure)),
  forall (result0: ((pointer) Z2)),
  forall (HW_7: result0 = (acc substruct_Z7 ma_structure)),
  forall (HW_8: (valid alloc0 result)),
  forall (result1: Z),
  forall (HW_9: result1 = (acc fst_Z8_0 result)),
  forall (HW_10: (valid alloc0 result0)),
  forall (fst_Z2_0: ((memory) Z Z2)),
  forall (HW_11: fst_Z2_0 = (upd fst_Z2 result0 result1)),
  (not_assigns alloc fst_Z8 fst_Z8_0 pset_empty) /\
  (not_assigns alloc fst_Z2 fst_Z2_0
   (pset_singleton (acc substruct_Z7 ma_structure))).
Proof.
intuition;subst;auto.
red;intros.
rewrite acc_upd_neq;auto.
intro;subst.
rewrite <- shift_zero in H10.
generalize H10.
apply fresh_not_valid.
auto.
red;intros.
rewrite acc_upd_neq;auto.
assert (p<> ma_structure # substruct_Z7).
apply pset_singleton_elim;auto.
auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y_0: Z),
  forall (HW_3: y_0 = 1),
  (* File "clash.c", line 12, characters 13-62 *) (((x = 0 -> y_0 = 1)) /\
  ((x <> 0 -> y_0 = 2))).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (x: Z),
  forall (HW_4: x <> 0),
  forall (y_0: Z),
  forall (HW_6: y_0 = 2),
  (* File "clash.c", line 12, characters 13-62 *) (((x = 0 -> y_0 = 1)) /\
  ((x <> 0 -> y_0 = 2))).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (y: Z),
  forall (y_0: Z),
  forall (HW_2: y_0 = 0),
  (* File "clash.c", line 5, characters 13-41 *) (y_0 = 0 /\ y = y).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_1 : 
  forall (x: Z),
  forall (y_0: Z),
  forall (HW_2: y_0 = 2),
  forall (HW_3: x = 0),
  forall (y_1: Z),
  forall (HW_5: y_1 = 1),
  (* File "clash.c", line 27, characters 13-65 *) (((x = 0 -> y_1 = 1)) /\
  ((x <> 0 -> y_1 = 2))).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_2 : 
  forall (x: Z),
  forall (y_0: Z),
  forall (HW_2: y_0 = 2),
  forall (HW_6: x <> 0),
  (* File "clash.c", line 27, characters 13-65 *) (((x = 0 -> y_0 = 1)) /\
  ((x <> 0 -> y_0 = 2))).
Proof.
intuition.
Save.

