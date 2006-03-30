(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export struct_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (A787:Set),
  forall (t2: ((pointer) A787)),
  forall (alloc: alloc_table),
  forall (pps: ((pointer) pps_14)),
  forall (ps: ((pointer) s_12)),
  forall (s: ((pointer) s_12)),
  forall (t_s_12: ((memory) ((pointer) t_2) s_12)),
  forall (x_t2_10: ((memory) Z A787)),
  forall (x_t_2: ((memory) Z t_2)),
  forall (y_t_2: ((memory) Z t_2)),
  forall (z_s_12: ((memory) Z s_12)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_t2_10 t2) = 0) /\
                (valid alloc s) /\ (constant_ps ps) /\ (valid alloc pps) /\
                (constant_s z_s_12 t_s_12 y_t_2 x_t_2 s alloc)),
  (valid alloc t2).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (A788:Set),
  forall (t2: ((pointer) A788)),
  forall (alloc: alloc_table),
  forall (pps: ((pointer) pps_14)),
  forall (ps: ((pointer) s_12)),
  forall (s: ((pointer) s_12)),
  forall (t_s_12: ((memory) ((pointer) t_2) s_12)),
  forall (x_t2_10: ((memory) Z A788)),
  forall (x_t_2: ((memory) Z t_2)),
  forall (y_t_2: ((memory) Z t_2)),
  forall (z_s_12: ((memory) Z s_12)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_t2_10 t2) = 0) /\
                (valid alloc s) /\ (constant_ps ps) /\ (valid alloc pps) /\
                (constant_s z_s_12 t_s_12 y_t_2 x_t_2 s alloc)),
  forall (HW_2: (valid alloc t2)),
  forall (result: Z),
  forall (HW_3: result = (acc x_t2_10 t2)),
  forall (x_t2_10_0: ((memory) Z A788)),
  forall (HW_4: x_t2_10_0 = (upd x_t2_10 t2 (result + 1))),
  forall (HW_5: (valid alloc t2)),
  forall (result0: Z),
  forall (HW_6: result0 = (acc x_t2_10_0 t2)),
  forall (x_t2_10_1: ((memory) Z A788)),
  forall (HW_7: x_t2_10_1 = (upd x_t2_10_0 t2 (1 + result0))),
  result0 = 1.
Proof.
intuition; subst; caduceus; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_3 : 
  forall (A789:Set),
  forall (t2: ((pointer) A789)),
  forall (alloc: alloc_table),
  forall (pps: ((pointer) pps_14)),
  forall (ps: ((pointer) s_12)),
  forall (s: ((pointer) s_12)),
  forall (t_s_12: ((memory) ((pointer) t_2) s_12)),
  forall (x_t2_10: ((memory) Z A789)),
  forall (x_t_2: ((memory) Z t_2)),
  forall (y_t_2: ((memory) Z t_2)),
  forall (z_s_12: ((memory) Z s_12)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_t2_10 t2) = 0) /\
                (valid alloc s) /\ (constant_ps ps) /\ (valid alloc pps) /\
                (constant_s z_s_12 t_s_12 y_t_2 x_t_2 s alloc)),
  forall (HW_2: (valid alloc t2)),
  forall (result: Z),
  forall (HW_3: result = (acc x_t2_10 t2)),
  forall (x_t2_10_0: ((memory) Z A789)),
  forall (HW_4: x_t2_10_0 = (upd x_t2_10 t2 (result + 1))),
  forall (HW_5: (valid alloc t2)),
  forall (result0: Z),
  forall (HW_6: result0 = (acc x_t2_10_0 t2)),
  forall (x_t2_10_1: ((memory) Z A789)),
  forall (HW_7: x_t2_10_1 = (upd x_t2_10_0 t2 (1 + result0))),
  (acc x_t2_10_1 t2) = 2.
Proof.
intuition;subst;caduceus.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_4 : 
  forall (A790:Set),
  forall (t2: ((pointer) A790)),
  forall (alloc: alloc_table),
  forall (pps: ((pointer) pps_14)),
  forall (ps: ((pointer) s_12)),
  forall (s: ((pointer) s_12)),
  forall (t_s_12: ((memory) ((pointer) t_2) s_12)),
  forall (x_t2_10: ((memory) Z A790)),
  forall (x_t_2: ((memory) Z t_2)),
  forall (y_t_2: ((memory) Z t_2)),
  forall (z_s_12: ((memory) Z s_12)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_t2_10 t2) = 0) /\
                (valid alloc s) /\ (constant_ps ps) /\ (valid alloc pps) /\
                (constant_s z_s_12 t_s_12 y_t_2 x_t_2 s alloc)),
  forall (HW_2: (valid alloc t2)),
  forall (result: Z),
  forall (HW_3: result = (acc x_t2_10 t2)),
  forall (x_t2_10_0: ((memory) Z A790)),
  forall (HW_4: x_t2_10_0 = (upd x_t2_10 t2 (result + 1))),
  forall (HW_5: (valid alloc t2)),
  forall (result0: Z),
  forall (HW_6: result0 = (acc x_t2_10_0 t2)),
  forall (x_t2_10_1: ((memory) Z A790)),
  forall (HW_7: x_t2_10_1 = (upd x_t2_10_0 t2 (1 + result0))),
  (not_assigns alloc x_t2_10 x_t2_10_1 (pset_singleton t2)).
Proof.
intuition;subst;caduceus.
red;intros.
assert (p<> t2).
apply pset_singleton_elim;auto.
rewrite acc_upd_neq;auto.
rewrite acc_upd_neq;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_5 : 
  forall (A791:Set),
  forall (t2: ((pointer) A791)),
  forall (alloc: alloc_table),
  forall (pps: ((pointer) pps_14)),
  forall (ps: ((pointer) s_12)),
  forall (s: ((pointer) s_12)),
  forall (t_s_12: ((memory) ((pointer) t_2) s_12)),
  forall (x_t2_10: ((memory) Z A791)),
  forall (x_t_2: ((memory) Z t_2)),
  forall (y_t2_10: ((memory) Z A791)),
  forall (y_t_2: ((memory) Z t_2)),
  forall (z_s_12: ((memory) Z s_12)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_t2_10 t2) = 0) /\
                (valid alloc s) /\ (constant_ps ps) /\ (valid alloc pps) /\
                (constant_s z_s_12 t_s_12 y_t_2 x_t_2 s alloc)),
  forall (HW_2: (valid alloc t2)),
  forall (result: Z),
  forall (HW_3: result = (acc x_t2_10 t2)),
  forall (x_t2_10_0: ((memory) Z A791)),
  forall (HW_4: x_t2_10_0 = (upd x_t2_10 t2 (result + 1))),
  forall (HW_5: (valid alloc t2)),
  forall (result0: Z),
  forall (HW_6: result0 = (acc x_t2_10_0 t2)),
  forall (x_t2_10_1: ((memory) Z A791)),
  forall (HW_7: x_t2_10_1 = (upd x_t2_10_0 t2 (1 + result0))),
  (not_assigns alloc y_t2_10 y_t2_10 pset_empty).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (SPPM_pps_14: ((memory) ((pointer) s_12) pps_14)),
  forall (alloc: alloc_table),
  forall (pps: ((pointer) pps_14)),
  forall (ps: ((pointer) s_12)),
  forall (s: ((pointer) s_12)),
  forall (t_s_12: ((memory) ((pointer) t_2) s_12)),
  forall (x_t_2: ((memory) Z t_2)),
  forall (y_t_2: ((memory) Z t_2)),
  forall (z_s_12: ((memory) Z s_12)),
  forall (HW_1: (* File "struct.c", line 21, characters 14-24 *)
                (valid alloc ps) /\ (valid alloc s) /\ (constant_ps ps) /\
                (valid alloc pps) /\
                (constant_s z_s_12 t_s_12 y_t_2 x_t_2 s alloc) /\
                (valid1 t_s_12) /\ (separation2 t_s_12 t_s_12)),
  forall (ps0: ((pointer) s_12)),
  forall (HW_3: ps0 = s),
  forall (SPPM_pps_14_0: ((memory) ((pointer) s_12) pps_14)),
  forall (HW_4: SPPM_pps_14_0 = (upd SPPM_pps_14 pps ps0)),
  forall (result: ((pointer) t_2)),
  forall (HW_5: result = (acc t_s_12 s)),
  forall (p: ((pointer) t_2)),
  forall (HW_6: p = result),
  (valid alloc ps0).
Proof.
 intuition.
subst; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (SPPM_pps_14: ((memory) ((pointer) s_12) pps_14)),
  forall (alloc: alloc_table),
  forall (pps: ((pointer) pps_14)),
  forall (ps: ((pointer) s_12)),
  forall (s: ((pointer) s_12)),
  forall (t_s_12: ((memory) ((pointer) t_2) s_12)),
  forall (x_t_2: ((memory) Z t_2)),
  forall (y_t_2: ((memory) Z t_2)),
  forall (z_s_12: ((memory) Z s_12)),
  forall (HW_1: (* File "struct.c", line 21, characters 14-24 *)
                (valid alloc ps) /\ (valid alloc s) /\ (constant_ps ps) /\
                (valid alloc pps) /\
                (constant_s z_s_12 t_s_12 y_t_2 x_t_2 s alloc) /\
                (valid1 t_s_12) /\ (separation2 t_s_12 t_s_12)),
  forall (ps0: ((pointer) s_12)),
  forall (HW_3: ps0 = s),
  forall (SPPM_pps_14_0: ((memory) ((pointer) s_12) pps_14)),
  forall (HW_4: SPPM_pps_14_0 = (upd SPPM_pps_14 pps ps0)),
  forall (result: ((pointer) t_2)),
  forall (HW_5: result = (acc t_s_12 s)),
  forall (p: ((pointer) t_2)),
  forall (HW_6: p = result),
  forall (HW_7: (valid alloc ps0)),
  forall (result0: ((pointer) t_2)),
  forall (HW_8: result0 = (acc t_s_12 ps0)),
  forall (x_t_2_0: ((memory) Z t_2)),
  forall (HW_9: x_t_2_0 = (upd x_t_2 result0 1)),
  forall (result1: ((pointer) t_2)),
  forall (HW_10: result1 = (acc t_s_12 s)),
  forall (result2: Z),
  forall (HW_11: result2 = (acc x_t_2_0 result1)),
  result2 = 1.
Proof.
intuition.
subst;auto.
caduceus.
Save.
