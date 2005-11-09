(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export ref_glob_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (x: ((pointer) Z9)),
  forall (HW_1: (valid_range alloc x 0 0)),
  (valid alloc x).
Proof.
intuition.
subst;auto.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f1_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (int_Z9: ((memory) Z Z9)),
  forall (x: ((pointer) Z9)),
  forall (HW_1: (valid_range alloc x 0 0)),
  forall (HW_2: (valid alloc x)),
  forall (int_Z9_0: ((memory) Z Z9)),
  forall (HW_3: int_Z9_0 = (upd int_Z9 x 1)),
  (* File "ref_glob.c", line 13, characters 13-19 *) (acc int_Z9_0 x) = 1 /\
  (not_assigns alloc int_Z9 int_Z9_0 (pset_singleton x)).
Proof.
intuition;subst; caduceus.
red.
intros.
rewrite acc_upd_neq;auto.
generalize (pset_singleton_elim _ _ H0);auto.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (x: ((pointer) Z9)),
  forall (HW_1: (valid_range alloc x 0 0)),
  (* File "ref_glob.c", line 2, characters 14-23 *) (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (int_Z9: ((memory) Z Z9)),
  forall (x: ((pointer) Z9)),
  forall (HW_1: (valid_range alloc x 0 0)),
  forall (HW_2: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc x)),
  forall (int_Z9_0: ((memory) Z Z9)),
  forall (HW_3: (* File "ref_glob.c", line 4, characters 13-20 *)
                (acc int_Z9_0 x) = 1 /\
                (not_assigns alloc int_Z9 int_Z9_0 (pset_singleton x))),
  (* File "ref_glob.c", line 20, characters 13-19 *) (acc int_Z9_0 x) = 1 /\
  (not_assigns alloc int_Z9 int_Z9_0 (pset_singleton x)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (plas: ((pointer) Z13)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas)),
  (valid alloc plas).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (c2_Z13: ((memory) ((pointer) Z9) Z13)),
  forall (plas: ((pointer) Z13)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) Z9)),
  forall (HW_3: result = (acc c2_Z13 plas)),
  (valid alloc result).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (c2_Z13: ((memory) ((pointer) Z9) Z13)),
  forall (int_Z9: ((memory) Z Z9)),
  forall (plas: ((pointer) Z13)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) Z9)),
  forall (HW_3: result = (acc c2_Z13 plas)),
  forall (HW_4: (valid alloc result)),
  forall (int_Z9_0: ((memory) Z Z9)),
  forall (HW_5: int_Z9_0 = (upd int_Z9 result 2)),
  (valid alloc plas).
Proof.
intuition.
subst.
rewrite H11;auto.
generalize (H2 plas alloc H).
intro.
apply pset_singleton_intro.
generalize (neq_base_addr_neq_shift (plas#c1) (plas#c2) 0 0 H4).
repeat rewrite shift_zero;auto.
subst;auto.
subst.
red.
intros.
rewrite H11;auto.
rewrite H8;auto.
rewrite acc_upd_neq;auto.
intro;subst.
generalize (pset_union_elim1 _  _ _  H6);auto.
apply not_not_in_pset_singleton.
generalize (pset_union_elim2 _  _ _  H6);auto.
generalize (pset_union_elim1 _ _ _ H6);auto.
subst;auto.
subst.
unfold valid1 in H5.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (c1_Z13: ((memory) ((pointer) Z9) Z13)),
  forall (c2_Z13: ((memory) ((pointer) Z9) Z13)),
  forall (int_Z9: ((memory) Z Z9)),
  forall (plas: ((pointer) Z13)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) Z9)),
  forall (HW_3: result = (acc c2_Z13 plas)),
  forall (HW_4: (valid alloc result)),
  forall (int_Z9_0: ((memory) Z Z9)),
  forall (HW_5: int_Z9_0 = (upd int_Z9 result 2)),
  forall (HW_6: (valid alloc plas)),
  forall (result0: ((pointer) Z9)),
  forall (HW_7: result0 = (acc c1_Z13 plas)),
  (* File "ref_glob.c", line 2, characters 14-23 *) (valid alloc result0).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (c1_Z13: ((memory) ((pointer) Z9) Z13)),
  forall (c2_Z13: ((memory) ((pointer) Z9) Z13)),
  forall (int_Z9: ((memory) Z Z9)),
  forall (plas: ((pointer) Z13)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) Z9)),
  forall (HW_3: result = (acc c2_Z13 plas)),
  forall (HW_4: (valid alloc result)),
  forall (int_Z9_0: ((memory) Z Z9)),
  forall (HW_5: int_Z9_0 = (upd int_Z9 result 2)),
  forall (HW_6: (valid alloc plas)),
  forall (result0: ((pointer) Z9)),
  forall (HW_7: result0 = (acc c1_Z13 plas)),
  forall (HW_8: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc result0)),
  forall (int_Z9_1: ((memory) Z Z9)),
  forall (HW_9: (* File "ref_glob.c", line 4, characters 13-20 *)
                (acc int_Z9_1 result0) = 1 /\
                (not_assigns alloc int_Z9_0 int_Z9_1 (pset_singleton result0))),
  (valid alloc plas).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_6 : 
  forall (alloc: alloc_table),
  forall (c1_Z13: ((memory) ((pointer) Z9) Z13)),
  forall (c2_Z13: ((memory) ((pointer) Z9) Z13)),
  forall (int_Z9: ((memory) Z Z9)),
  forall (plas: ((pointer) Z13)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) Z9)),
  forall (HW_3: result = (acc c2_Z13 plas)),
  forall (HW_4: (valid alloc result)),
  forall (int_Z9_0: ((memory) Z Z9)),
  forall (HW_5: int_Z9_0 = (upd int_Z9 result 2)),
  forall (HW_6: (valid alloc plas)),
  forall (result0: ((pointer) Z9)),
  forall (HW_7: result0 = (acc c1_Z13 plas)),
  forall (HW_8: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc result0)),
  forall (int_Z9_1: ((memory) Z Z9)),
  forall (HW_9: (* File "ref_glob.c", line 4, characters 13-20 *)
                (acc int_Z9_1 result0) = 1 /\
                (not_assigns alloc int_Z9_0 int_Z9_1 (pset_singleton result0))),
  forall (HW_10: (valid alloc plas)),
  forall (result1: ((pointer) Z9)),
  forall (HW_11: result1 = (acc c2_Z13 plas)),
  (* File "ref_glob.c", line 2, characters 14-23 *) (valid alloc result1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_7 : 
  forall (alloc: alloc_table),
  forall (c1_Z13: ((memory) ((pointer) Z9) Z13)),
  forall (c2_Z13: ((memory) ((pointer) Z9) Z13)),
  forall (int_Z9: ((memory) Z Z9)),
  forall (plas: ((pointer) Z13)),
  forall (HW_1: (* File "ref_glob.c", line 30, characters 14-26 *)
                (valid alloc plas)),
  forall (HW_2: (valid alloc plas)),
  forall (result: ((pointer) Z9)),
  forall (HW_3: result = (acc c2_Z13 plas)),
  forall (HW_4: (valid alloc result)),
  forall (int_Z9_0: ((memory) Z Z9)),
  forall (HW_5: int_Z9_0 = (upd int_Z9 result 2)),
  forall (HW_6: (valid alloc plas)),
  forall (result0: ((pointer) Z9)),
  forall (HW_7: result0 = (acc c1_Z13 plas)),
  forall (HW_8: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc result0)),
  forall (int_Z9_1: ((memory) Z Z9)),
  forall (HW_9: (* File "ref_glob.c", line 4, characters 13-20 *)
                (acc int_Z9_1 result0) = 1 /\
                (not_assigns alloc int_Z9_0 int_Z9_1 (pset_singleton result0))),
  forall (HW_10: (valid alloc plas)),
  forall (result1: ((pointer) Z9)),
  forall (HW_11: result1 = (acc c2_Z13 plas)),
  forall (HW_12: (* File "ref_glob.c", line 2, characters 14-23 *)
                 (valid alloc result1)),
  forall (int_Z9_2: ((memory) Z Z9)),
  forall (HW_13: (* File "ref_glob.c", line 4, characters 13-20 *)
                 (acc int_Z9_2 result1) = 1 /\
                 (not_assigns alloc int_Z9_1 int_Z9_2
                  (pset_singleton result1))),
  (* File "ref_glob.c", line 32, characters 13-43 *)
  ((acc int_Z9_2 (acc c1_Z13 plas)) = 1 /\ (acc int_Z9_2 (acc c2_Z13 plas)) =
  1) /\
  (not_assigns alloc int_Z9 int_Z9_2
   (pset_union (pset_singleton (acc c2_Z13 plas))
    (pset_singleton (acc c1_Z13 plas)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (p: ((pointer) Z9)),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc p)),
  (valid alloc p).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (p: ((pointer) Z9)),
  forall (alloc: alloc_table),
  forall (int_Z9: ((memory) Z Z9)),
  forall (HW_1: (* File "ref_glob.c", line 2, characters 14-23 *)
                (valid alloc p)),
  forall (HW_2: (valid alloc p)),
  forall (int_Z9_0: ((memory) Z Z9)),
  forall (HW_3: int_Z9_0 = (upd int_Z9 p 1)),
  (* File "ref_glob.c", line 4, characters 13-20 *) (acc int_Z9_0 p) = 1 /\
  (not_assigns alloc int_Z9 int_Z9_0 (pset_singleton p)).
Proof.
intuition.
subst; caduceus.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_1 : 
  forall (p: ((pointer) Z16)),
  forall (alloc: alloc_table),
  forall (int_Z17_Z16: ((memory) ((pointer) Z17) Z16)),
  forall (HW_1: (* File "ref_glob.c", line 45, characters 14-38 *)
                ((valid alloc p) /\ (valid alloc (acc int_Z17_Z16 p)))),
  (valid alloc p).
Proof.
intuition;subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_2 : 
  forall (p: ((pointer) Z16)),
  forall (alloc: alloc_table),
  forall (int_Z17_Z16: ((memory) ((pointer) Z17) Z16)),
  forall (HW_1: (* File "ref_glob.c", line 45, characters 14-38 *)
                ((valid alloc p) /\ (valid alloc (acc int_Z17_Z16 p)))),
  forall (HW_2: (valid alloc p)),
  forall (result: ((pointer) Z17)),
  forall (HW_3: result = (acc int_Z17_Z16 p)),
  (valid alloc result).
Proof.
intuition;subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_3 : 
  forall (p: ((pointer) Z16)),
  forall (alloc: alloc_table),
  forall (int_Z17: ((memory) Z Z17)),
  forall (int_Z17_Z16: ((memory) ((pointer) Z17) Z16)),
  forall (HW_1: (* File "ref_glob.c", line 45, characters 14-38 *)
                ((valid alloc p) /\ (valid alloc (acc int_Z17_Z16 p)))),
  forall (HW_2: (valid alloc p)),
  forall (result: ((pointer) Z17)),
  forall (HW_3: result = (acc int_Z17_Z16 p)),
  forall (HW_4: (valid alloc result)),
  forall (int_Z17_0: ((memory) Z Z17)),
  forall (HW_5: int_Z17_0 = (upd int_Z17 result 2)),
  (* File "ref_glob.c", line 47, characters 13-21 *)
  (acc int_Z17_0 (acc int_Z17_Z16 p)) = 2 /\
  (not_assigns alloc int_Z17 int_Z17_0 (pset_singleton (acc int_Z17_Z16 p))).
Proof.
intuition; subst; caduceus.
red;intros.
rewrite acc_upd_neq;auto.
generalize (pset_singleton_elim _ _ H2);auto.
Save.

