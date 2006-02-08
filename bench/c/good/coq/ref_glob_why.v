(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export ref_glob_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intM_x_11: ((memory) Z x_11)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (valid alloc x) /\ (valid_range alloc t 0 2) /\
                (constant_plas plas) /\ (constant_x x alloc)),
  forall (intM_x_11_0: ((memory) Z x_11)),
  forall (HW_2: intM_x_11_0 = (upd intM_x_11 x 1)),
  (* File "ref_glob.c", line 13, characters 13-19 *) (acc intM_x_11_0 x) = 1.
Proof.
intuition.
Qed.

Proof.
intuition;subst; caduceus.
red.
intros.
rewrite acc_upd_neq;auto.
generalize (pset_singleton_elim H0);auto.
Qed.

Proof.
intuition.
Save.


Proof.
intuition.
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f1_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intM_x_11: ((memory) Z x_11)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (valid alloc x) /\ (valid_range alloc t 0 2) /\
                (constant_plas plas) /\ (constant_x x alloc)),
  forall (intM_x_11_0: ((memory) Z x_11)),
  forall (HW_2: intM_x_11_0 = (upd intM_x_11 x 1)),
  (not_assigns alloc intM_x_11 intM_x_11_0 (pset_singleton x)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (c1_plas_12: ((memory) ((pointer) c1_9) plas_12)),
  forall (c2_plas_12: ((memory) ((pointer) c2_8) plas_12)),
  forall (intM_c2_8: ((memory) Z c2_8)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas) /\ (valid alloc x) /\
                (valid_range alloc t 0 2) /\ (constant_plas plas) /\
                (constant_x x alloc) /\ (valid1_range c2_plas_12 1) /\
                (valid1_range c1_plas_12 1) /\ (valid1 c2_plas_12) /\
                (valid1 c1_plas_12)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) c2_8)),
  forall (HW_3: result = (acc c2_plas_12 plas)),
  forall (intM_c2_8_0: ((memory) Z c2_8)),
  forall (HW_4: intM_c2_8_0 = (upd intM_c2_8 result 2)),
  forall (HW_5: (valid alloc plas)),
  forall (result0: ((pointer) c1_9)),
  forall (HW_6: result0 = (acc c1_plas_12 plas)),
  (* File "ref_glob.c", line 2, characters 14-23 *) (valid alloc result0).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (c1_plas_12: ((memory) ((pointer) c1_9) plas_12)),
  forall (c2_plas_12: ((memory) ((pointer) c2_8) plas_12)),
  forall (intM_c1_9: ((memory) Z c1_9)),
  forall (intM_c2_8: ((memory) Z c2_8)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas) /\ (valid alloc x) /\
                (valid_range alloc t 0 2) /\ (constant_plas plas) /\
                (constant_x x alloc) /\ (valid1_range c2_plas_12 1) /\
                (valid1_range c1_plas_12 1) /\ (valid1 c2_plas_12) /\
                (valid1 c1_plas_12)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) c2_8)),
  forall (HW_3: result = (acc c2_plas_12 plas)),
  forall (intM_c2_8_0: ((memory) Z c2_8)),
  forall (HW_4: intM_c2_8_0 = (upd intM_c2_8 result 2)),
  forall (HW_5: (valid alloc plas)),
  forall (result0: ((pointer) c1_9)),
  forall (HW_6: result0 = (acc c1_plas_12 plas)),
  forall (HW_7: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc result0)),
  forall (intM_c1_9_0: ((memory) Z c1_9)),
  forall (HW_8: (* File "ref_glob.c", line 4, characters 13-20 *)
                (acc intM_c1_9_0 result0) = 1 /\
                (not_assigns alloc intM_c1_9 intM_c1_9_0
                 (pset_singleton result0))),
  forall (HW_9: (valid alloc plas)),
  forall (result1: ((pointer) c2_8)),
  forall (HW_10: result1 = (acc c2_plas_12 plas)),
  (* File "ref_glob.c", line 2, characters 14-23 *) (valid alloc result1).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (c1_plas_12: ((memory) ((pointer) c1_9) plas_12)),
  forall (c2_plas_12: ((memory) ((pointer) c2_8) plas_12)),
  forall (intM_c1_9: ((memory) Z c1_9)),
  forall (intM_c2_8: ((memory) Z c2_8)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas) /\ (valid alloc x) /\
                (valid_range alloc t 0 2) /\ (constant_plas plas) /\
                (constant_x x alloc) /\ (valid1_range c2_plas_12 1) /\
                (valid1_range c1_plas_12 1) /\ (valid1 c2_plas_12) /\
                (valid1 c1_plas_12)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) c2_8)),
  forall (HW_3: result = (acc c2_plas_12 plas)),
  forall (intM_c2_8_0: ((memory) Z c2_8)),
  forall (HW_4: intM_c2_8_0 = (upd intM_c2_8 result 2)),
  forall (HW_5: (valid alloc plas)),
  forall (result0: ((pointer) c1_9)),
  forall (HW_6: result0 = (acc c1_plas_12 plas)),
  forall (HW_7: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc result0)),
  forall (intM_c1_9_0: ((memory) Z c1_9)),
  forall (HW_8: (* File "ref_glob.c", line 4, characters 13-20 *)
                (acc intM_c1_9_0 result0) = 1 /\
                (not_assigns alloc intM_c1_9 intM_c1_9_0
                 (pset_singleton result0))),
  forall (HW_9: (valid alloc plas)),
  forall (result1: ((pointer) c2_8)),
  forall (HW_10: result1 = (acc c2_plas_12 plas)),
  forall (HW_11: (* File "ref_glob.c", line 2, characters 14-23 *)
                 (valid alloc result1)),
  forall (intM_c2_8_1: ((memory) Z c2_8)),
  forall (HW_12: (* File "ref_glob.c", line 4, characters 13-20 *)
                 (acc intM_c2_8_1 result1) = 1 /\
                 (not_assigns alloc intM_c2_8_0 intM_c2_8_1
                  (pset_singleton result1))),
  (acc intM_c1_9_0 (acc c1_plas_12 plas)) = 1.
Proof.
intuition.
Save.

Proof.
intuition.
subst;auto.
Save.

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
rewrite H8;auto.
apply pset_singleton_intro.
red in H2.
replace (plas # c1_Z12 <> plas # c2_Z12) with (shift (plas # c1_Z12) 0 <> shift (plas # c2_Z12) 0).
apply neq_base_addr_neq_shift.
apply H2 with alloc;auto.
rewrite shift_zero;rewrite shift_zero;auto.
subst;auto.
red;intros.
rewrite H8;auto.
rewrite H6;auto.
subst.
rewrite acc_upd_neq;auto.
generalize (pset_union_elim1 H10);intro.
assert (p<> plas # c2_Z12).
apply pset_singleton_elim;auto.
auto.
subst.
generalize (pset_union_elim2 H10);auto.
subst.
generalize (pset_union_elim1 H10);auto.
Save.

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

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (c1_plas_12: ((memory) ((pointer) c1_9) plas_12)),
  forall (c2_plas_12: ((memory) ((pointer) c2_8) plas_12)),
  forall (intM_c1_9: ((memory) Z c1_9)),
  forall (intM_c2_8: ((memory) Z c2_8)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas) /\ (valid alloc x) /\
                (valid_range alloc t 0 2) /\ (constant_plas plas) /\
                (constant_x x alloc) /\ (valid1_range c2_plas_12 1) /\
                (valid1_range c1_plas_12 1) /\ (valid1 c2_plas_12) /\
                (valid1 c1_plas_12)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) c2_8)),
  forall (HW_3: result = (acc c2_plas_12 plas)),
  forall (intM_c2_8_0: ((memory) Z c2_8)),
  forall (HW_4: intM_c2_8_0 = (upd intM_c2_8 result 2)),
  forall (HW_5: (valid alloc plas)),
  forall (result0: ((pointer) c1_9)),
  forall (HW_6: result0 = (acc c1_plas_12 plas)),
  forall (HW_7: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc result0)),
  forall (intM_c1_9_0: ((memory) Z c1_9)),
  forall (HW_8: (* File "ref_glob.c", line 4, characters 13-20 *)
                (acc intM_c1_9_0 result0) = 1 /\
                (not_assigns alloc intM_c1_9 intM_c1_9_0
                 (pset_singleton result0))),
  forall (HW_9: (valid alloc plas)),
  forall (result1: ((pointer) c2_8)),
  forall (HW_10: result1 = (acc c2_plas_12 plas)),
  forall (HW_11: (* File "ref_glob.c", line 2, characters 14-23 *)
                 (valid alloc result1)),
  forall (intM_c2_8_1: ((memory) Z c2_8)),
  forall (HW_12: (* File "ref_glob.c", line 4, characters 13-20 *)
                 (acc intM_c2_8_1 result1) = 1 /\
                 (not_assigns alloc intM_c2_8_0 intM_c2_8_1
                  (pset_singleton result1))),
  (acc intM_c2_8_1 (acc c2_plas_12 plas)) = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (c1_plas_12: ((memory) ((pointer) c1_9) plas_12)),
  forall (c2_plas_12: ((memory) ((pointer) c2_8) plas_12)),
  forall (intM_c1_9: ((memory) Z c1_9)),
  forall (intM_c2_8: ((memory) Z c2_8)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas) /\ (valid alloc x) /\
                (valid_range alloc t 0 2) /\ (constant_plas plas) /\
                (constant_x x alloc) /\ (valid1_range c2_plas_12 1) /\
                (valid1_range c1_plas_12 1) /\ (valid1 c2_plas_12) /\
                (valid1 c1_plas_12)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) c2_8)),
  forall (HW_3: result = (acc c2_plas_12 plas)),
  forall (intM_c2_8_0: ((memory) Z c2_8)),
  forall (HW_4: intM_c2_8_0 = (upd intM_c2_8 result 2)),
  forall (HW_5: (valid alloc plas)),
  forall (result0: ((pointer) c1_9)),
  forall (HW_6: result0 = (acc c1_plas_12 plas)),
  forall (HW_7: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc result0)),
  forall (intM_c1_9_0: ((memory) Z c1_9)),
  forall (HW_8: (* File "ref_glob.c", line 4, characters 13-20 *)
                (acc intM_c1_9_0 result0) = 1 /\
                (not_assigns alloc intM_c1_9 intM_c1_9_0
                 (pset_singleton result0))),
  forall (HW_9: (valid alloc plas)),
  forall (result1: ((pointer) c2_8)),
  forall (HW_10: result1 = (acc c2_plas_12 plas)),
  forall (HW_11: (* File "ref_glob.c", line 2, characters 14-23 *)
                 (valid alloc result1)),
  forall (intM_c2_8_1: ((memory) Z c2_8)),
  forall (HW_12: (* File "ref_glob.c", line 4, characters 13-20 *)
                 (acc intM_c2_8_1 result1) = 1 /\
                 (not_assigns alloc intM_c2_8_0 intM_c2_8_1
                  (pset_singleton result1))),
  (not_assigns alloc c1_plas_12 c1_plas_12 pset_empty).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_6 : 
  forall (alloc: alloc_table),
  forall (c1_plas_12: ((memory) ((pointer) c1_9) plas_12)),
  forall (c2_plas_12: ((memory) ((pointer) c2_8) plas_12)),
  forall (intM_c1_9: ((memory) Z c1_9)),
  forall (intM_c2_8: ((memory) Z c2_8)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas) /\ (valid alloc x) /\
                (valid_range alloc t 0 2) /\ (constant_plas plas) /\
                (constant_x x alloc) /\ (valid1_range c2_plas_12 1) /\
                (valid1_range c1_plas_12 1) /\ (valid1 c2_plas_12) /\
                (valid1 c1_plas_12)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) c2_8)),
  forall (HW_3: result = (acc c2_plas_12 plas)),
  forall (intM_c2_8_0: ((memory) Z c2_8)),
  forall (HW_4: intM_c2_8_0 = (upd intM_c2_8 result 2)),
  forall (HW_5: (valid alloc plas)),
  forall (result0: ((pointer) c1_9)),
  forall (HW_6: result0 = (acc c1_plas_12 plas)),
  forall (HW_7: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc result0)),
  forall (intM_c1_9_0: ((memory) Z c1_9)),
  forall (HW_8: (* File "ref_glob.c", line 4, characters 13-20 *)
                (acc intM_c1_9_0 result0) = 1 /\
                (not_assigns alloc intM_c1_9 intM_c1_9_0
                 (pset_singleton result0))),
  forall (HW_9: (valid alloc plas)),
  forall (result1: ((pointer) c2_8)),
  forall (HW_10: result1 = (acc c2_plas_12 plas)),
  forall (HW_11: (* File "ref_glob.c", line 2, characters 14-23 *)
                 (valid alloc result1)),
  forall (intM_c2_8_1: ((memory) Z c2_8)),
  forall (HW_12: (* File "ref_glob.c", line 4, characters 13-20 *)
                 (acc intM_c2_8_1 result1) = 1 /\
                 (not_assigns alloc intM_c2_8_0 intM_c2_8_1
                  (pset_singleton result1))),
  (not_assigns alloc c2_plas_12 c2_plas_12 pset_empty).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_7 : 
  forall (alloc: alloc_table),
  forall (c1_plas_12: ((memory) ((pointer) c1_9) plas_12)),
  forall (c2_plas_12: ((memory) ((pointer) c2_8) plas_12)),
  forall (intM_c1_9: ((memory) Z c1_9)),
  forall (intM_c2_8: ((memory) Z c2_8)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas) /\ (valid alloc x) /\
                (valid_range alloc t 0 2) /\ (constant_plas plas) /\
                (constant_x x alloc) /\ (valid1_range c2_plas_12 1) /\
                (valid1_range c1_plas_12 1) /\ (valid1 c2_plas_12) /\
                (valid1 c1_plas_12)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) c2_8)),
  forall (HW_3: result = (acc c2_plas_12 plas)),
  forall (intM_c2_8_0: ((memory) Z c2_8)),
  forall (HW_4: intM_c2_8_0 = (upd intM_c2_8 result 2)),
  forall (HW_5: (valid alloc plas)),
  forall (result0: ((pointer) c1_9)),
  forall (HW_6: result0 = (acc c1_plas_12 plas)),
  forall (HW_7: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc result0)),
  forall (intM_c1_9_0: ((memory) Z c1_9)),
  forall (HW_8: (* File "ref_glob.c", line 4, characters 13-20 *)
                (acc intM_c1_9_0 result0) = 1 /\
                (not_assigns alloc intM_c1_9 intM_c1_9_0
                 (pset_singleton result0))),
  forall (HW_9: (valid alloc plas)),
  forall (result1: ((pointer) c2_8)),
  forall (HW_10: result1 = (acc c2_plas_12 plas)),
  forall (HW_11: (* File "ref_glob.c", line 2, characters 14-23 *)
                 (valid alloc result1)),
  forall (intM_c2_8_1: ((memory) Z c2_8)),
  forall (HW_12: (* File "ref_glob.c", line 4, characters 13-20 *)
                 (acc intM_c2_8_1 result1) = 1 /\
                 (not_assigns alloc intM_c2_8_0 intM_c2_8_1
                  (pset_singleton result1))),
  (not_assigns alloc intM_c1_9 intM_c1_9_0
   (pset_singleton (acc c1_plas_12 plas))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_8 : 
  forall (alloc: alloc_table),
  forall (c1_plas_12: ((memory) ((pointer) c1_9) plas_12)),
  forall (c2_plas_12: ((memory) ((pointer) c2_8) plas_12)),
  forall (intM_c1_9: ((memory) Z c1_9)),
  forall (intM_c2_8: ((memory) Z c2_8)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas) /\ (valid alloc x) /\
                (valid_range alloc t 0 2) /\ (constant_plas plas) /\
                (constant_x x alloc) /\ (valid1_range c2_plas_12 1) /\
                (valid1_range c1_plas_12 1) /\ (valid1 c2_plas_12) /\
                (valid1 c1_plas_12)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) c2_8)),
  forall (HW_3: result = (acc c2_plas_12 plas)),
  forall (intM_c2_8_0: ((memory) Z c2_8)),
  forall (HW_4: intM_c2_8_0 = (upd intM_c2_8 result 2)),
  forall (HW_5: (valid alloc plas)),
  forall (result0: ((pointer) c1_9)),
  forall (HW_6: result0 = (acc c1_plas_12 plas)),
  forall (HW_7: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc result0)),
  forall (intM_c1_9_0: ((memory) Z c1_9)),
  forall (HW_8: (* File "ref_glob.c", line 4, characters 13-20 *)
                (acc intM_c1_9_0 result0) = 1 /\
                (not_assigns alloc intM_c1_9 intM_c1_9_0
                 (pset_singleton result0))),
  forall (HW_9: (valid alloc plas)),
  forall (result1: ((pointer) c2_8)),
  forall (HW_10: result1 = (acc c2_plas_12 plas)),
  forall (HW_11: (* File "ref_glob.c", line 2, characters 14-23 *)
                 (valid alloc result1)),
  forall (intM_c2_8_1: ((memory) Z c2_8)),
  forall (HW_12: (* File "ref_glob.c", line 4, characters 13-20 *)
                 (acc intM_c2_8_1 result1) = 1 /\
                 (not_assigns alloc intM_c2_8_0 intM_c2_8_1
                  (pset_singleton result1))),
  (not_assigns alloc intM_c2_8 intM_c2_8_1
   (pset_singleton (acc c2_plas_12 plas))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (A895:Set),
  forall (p: ((pointer) A895)),
  forall (alloc: alloc_table),
  forall (intM_p_10: ((memory) Z A895)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc p) /\ (valid alloc x) /\
                (valid_range alloc t 0 2) /\ (constant_plas plas) /\
                (constant_x x alloc)),
  forall (HW_2: (valid alloc p)),
  forall (intM_p_10_0: ((memory) Z A895)),
  forall (HW_3: intM_p_10_0 = (upd intM_p_10 p 1)),
  (* File "ref_glob.c", line 4, characters 13-20 *) (acc intM_p_10_0 p) = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (A896:Set),
  forall (p: ((pointer) A896)),
  forall (alloc: alloc_table),
  forall (intM_p_10: ((memory) Z A896)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc p) /\ (valid alloc x) /\
                (valid_range alloc t 0 2) /\ (constant_plas plas) /\
                (constant_x x alloc)),
  forall (HW_2: (valid alloc p)),
  forall (intM_p_10_0: ((memory) Z A896)),
  forall (HW_3: intM_p_10_0 = (upd intM_p_10 p 1)),
  (not_assigns alloc intM_p_10 intM_p_10_0 (pset_singleton p)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_1 : 
  forall (A897:Set),
  forall (p: ((pointer) A897)),
  forall (alloc: alloc_table),
  forall (intPM_p_14: ((memory) ((pointer) intPM_15) A897)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 45, characters 14-38 *)
                ((valid alloc p) /\ (valid alloc (acc intPM_p_14 p))) /\
                (valid alloc x) /\ (valid_range alloc t 0 2) /\
                (constant_plas plas) /\ (constant_x x alloc)),
  (valid alloc p).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_2 : 
  forall (A898:Set),
  forall (p: ((pointer) A898)),
  forall (alloc: alloc_table),
  forall (intPM_p_14: ((memory) ((pointer) intPM_15) A898)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 45, characters 14-38 *)
                ((valid alloc p) /\ (valid alloc (acc intPM_p_14 p))) /\
                (valid alloc x) /\ (valid_range alloc t 0 2) /\
                (constant_plas plas) /\ (constant_x x alloc)),
  forall (HW_2: (valid alloc p)),
  forall (result: ((pointer) intPM_15)),
  forall (HW_3: result = (acc intPM_p_14 p)),
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_3 : 
  forall (A899:Set),
  forall (p: ((pointer) A899)),
  forall (alloc: alloc_table),
  forall (intM_intPM_15: ((memory) Z intPM_15)),
  forall (intPM_p_14: ((memory) ((pointer) intPM_15) A899)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 45, characters 14-38 *)
                ((valid alloc p) /\ (valid alloc (acc intPM_p_14 p))) /\
                (valid alloc x) /\ (valid_range alloc t 0 2) /\
                (constant_plas plas) /\ (constant_x x alloc)),
  forall (HW_2: (valid alloc p)),
  forall (result: ((pointer) intPM_15)),
  forall (HW_3: result = (acc intPM_p_14 p)),
  forall (HW_4: (valid alloc result)),
  forall (intM_intPM_15_0: ((memory) Z intPM_15)),
  forall (HW_5: intM_intPM_15_0 = (upd intM_intPM_15 result 2)),
  (* File "ref_glob.c", line 47, characters 13-21 *)
  (acc intM_intPM_15_0 (acc intPM_p_14 p)) = 2.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_4 : 
  forall (A900:Set),
  forall (p: ((pointer) A900)),
  forall (alloc: alloc_table),
  forall (intM_intPM_15: ((memory) Z intPM_15)),
  forall (intPM_p_14: ((memory) ((pointer) intPM_15) A900)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 45, characters 14-38 *)
                ((valid alloc p) /\ (valid alloc (acc intPM_p_14 p))) /\
                (valid alloc x) /\ (valid_range alloc t 0 2) /\
                (constant_plas plas) /\ (constant_x x alloc)),
  forall (HW_2: (valid alloc p)),
  forall (result: ((pointer) intPM_15)),
  forall (HW_3: result = (acc intPM_p_14 p)),
  forall (HW_4: (valid alloc result)),
  forall (intM_intPM_15_0: ((memory) Z intPM_15)),
  forall (HW_5: intM_intPM_15_0 = (upd intM_intPM_15 result 2)),
  (not_assigns alloc intM_intPM_15 intM_intPM_15_0
   (pset_singleton (acc intPM_p_14 p))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_5 : 
  forall (A901:Set),
  forall (p: ((pointer) A901)),
  forall (alloc: alloc_table),
  forall (intM_intPM_15: ((memory) Z intPM_15)),
  forall (intPM_p_14: ((memory) ((pointer) intPM_15) A901)),
  forall (plas: ((pointer) plas_12)),
  forall (t: ((pointer) t_13)),
  forall (x: ((pointer) x_11)),
  forall (HW_1: (* File "ref_glob.c", line 45, characters 14-38 *)
                ((valid alloc p) /\ (valid alloc (acc intPM_p_14 p))) /\
                (valid alloc x) /\ (valid_range alloc t 0 2) /\
                (constant_plas plas) /\ (constant_x x alloc)),
  forall (HW_2: (valid alloc p)),
  forall (result: ((pointer) intPM_15)),
  forall (HW_3: result = (acc intPM_p_14 p)),
  forall (HW_4: (valid alloc result)),
  forall (intM_intPM_15_0: ((memory) Z intPM_15)),
  forall (HW_5: intM_intPM_15_0 = (upd intM_intPM_15 result 2)),
  (not_assigns alloc intPM_p_14 intPM_p_14 pset_empty).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

