(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export clash_spec_why.

(* Why obligation from file "why/clash.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f1_impl_po_1 : 
  forall (ma_structure: pointer),
  forall (alloc: alloc_table),
  forall (toto: ((memory) Z)),
  forall (HW_1: (valid alloc ma_structure) /\ (valid alloc ma_structure)),
  forall (toto_0: Z),
  forall (HW_3: toto_0 = 0),
  forall (toto0: ((memory) Z)),
  forall (HW_4: toto0 = (upd toto ma_structure toto_0)),
  (not_assigns alloc toto toto0 (pset_singleton ma_structure)).
Proof.
intuition.
Save.

(* Why obligation from file "why/clash.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_1 : 
  forall (ma_structure: pointer),
  forall (alloc: alloc_table),
  forall (fst: ((memory) Z)),
  forall (substruct: ((memory) pointer)),
  forall (HW_1: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                (valid alloc (acc substruct ma_structure))) /\
                (valid1 substruct) /\ (separation2 substruct substruct)),
  forall (result: pointer),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (fst0: ((memory) Z)),
  forall (HW_3: fst0 = (upd fst result 0)),
  forall (result0: pointer),
  forall (HW_4: result0 = (acc substruct ma_structure)),
  forall (result1: Z),
  forall (HW_5: result1 = (acc fst0 result)),
  forall (fst1: ((memory) Z)),
  forall (HW_6: fst1 = (upd fst0 result0 result1)),
  (not_assigns alloc fst fst1 (pset_singleton (acc substruct ma_structure))).
Proof.
intuition.
Save.

(* Why obligation from file "why/clash.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_2 : 
  forall (ma_structure: pointer),
  forall (alloc: alloc_table),
  forall (fst: ((memory) Z)),
  forall (substruct: ((memory) pointer)),
  forall (HW_1: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                (valid alloc (acc substruct ma_structure))) /\
                (valid1 substruct) /\ (separation2 substruct substruct)),
  forall (result: pointer),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (fst0: ((memory) Z)),
  forall (HW_3: fst0 = (upd fst result 0)),
  forall (result0: pointer),
  forall (HW_4: result0 = (acc substruct ma_structure)),
  forall (result1: Z),
  forall (HW_5: result1 = (acc fst0 result)),
  (valid alloc0 result0).
Proof.
intuition.
apply alloc_stack_valid with substruct_0 alloc; auto.

Save.

(* Why obligation from file "why/clash.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_3 : 
  forall (ma_structure: pointer),
  forall (alloc: alloc_table),
  forall (fst: ((memory) Z)),
  forall (substruct: ((memory) pointer)),
  forall (HW_1: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                (valid alloc (acc substruct ma_structure))) /\
                (valid1 substruct) /\ (separation2 substruct substruct)),
  forall (result: pointer),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (fst0: ((memory) Z)),
  forall (HW_3: fst0 = (upd fst result 0)),
  (valid alloc0 ma_structure).
Proof.
intuition.
subst; apply alloc_stack_valid with substruct_0 alloc; auto.
Save.

(* Why obligation from file "why/clash.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_4 : 
  forall (ma_structure: pointer),
  forall (alloc: alloc_table),
  forall (substruct: ((memory) pointer)),
  forall (HW_1: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                (valid alloc (acc substruct ma_structure))) /\
                (valid1 substruct) /\ (separation2 substruct substruct)),
  1 >= 1.
Proof.
intros.
unfold not_assigns.
intros.
subst.
caduceus.
rewrite acc_upd_neq;generalize (pset_singleton_elim p (ma_structure # substruct) H0);auto.
intro.
rewrite acc_upd_neq;auto.
inversion_clear Post9.
inversion_clear H3.
inversion_clear H5.
inversion_clear H6.
inversion_clear H7.
inversion_clear H8.
generalize (fresh_not_valid _ _ H6 0).
intros.
intro.
rewrite shift_zero in H8.
apply H8;subst;auto.
Save.



(* Why obligation from file "why/clash.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (x: Z),
  forall (HW_1: x = 0),
  forall (y_0: Z),
  forall (HW_3: y_0 = 1),
  (* File \"clash.c819618234.c1069824147.i\", line 0, characters 9-58 *)
  (((x = 0 -> y_0 = 1)) /\ ((x <> 0 -> y_0 = 2))).
Proof.
intuition.
Save.

(* Why obligation from file "why/clash.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (x: Z),
  forall (HW_4: x <> 0),
  forall (y_0: Z),
  forall (HW_6: y_0 = 2),
  (* File \"clash.c819618234.c1069824147.i\", line 0, characters 9-58 *)
  (((x = 0 -> y_0 = 1)) /\ ((x <> 0 -> y_0 = 2))).
Proof.
intuition.
Save.

(* Why obligation from file "why/clash.why", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (y: Z),
  forall (y_0: Z),
  forall (HW_2: y_0 = 0),
  (* File \"clash.c819618234.c1069824147.i\", line 0, characters 9-37 *)
  (y_0 = 0 /\ y = y).
Proof.
intuition.
Save.

(* Why obligation from file "why/clash.why", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_1 : 
  forall (x: Z),
  forall (y_0: Z),
  forall (HW_2: y_0 = 2),
  forall (HW_3: x = 0),
  forall (y_1: Z),
  forall (HW_5: y_1 = 1),
  (* File \"clash.c819618234.c1069824147.i\", line 0, characters 9-61 *)
  (((x = 0 -> y_1 = 1)) /\ ((x <> 0 -> y_1 = 2))).
Proof.
intuition.
Save.

(* Why obligation from file "why/clash.why", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_2 : 
  forall (x: Z),
  forall (y_0: Z),
  forall (HW_2: y_0 = 2),
  forall (HW_6: x <> 0),
  (* File \"clash.c819618234.c1069824147.i\", line 0, characters 9-61 *)
  (((x = 0 -> y_0 = 1)) /\ ((x <> 0 -> y_0 = 2))).
Proof.
intuition.
Save.

