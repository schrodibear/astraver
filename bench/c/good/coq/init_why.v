(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export init_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (a_s_9: ((memory) Z s_9)),
  forall (alloc: alloc_table),
  forall (b_s_9: ((memory) ((pointer) b_2) s_9)),
  forall (intM_b_2: ((memory) Z b_2)),
  forall (intM_t_7: ((memory) Z t_7)),
  forall (s: ((pointer) s_9)),
  forall (t: ((pointer) t_7)),
  forall (x: Z),
  forall (HW_1: ((* File "init.c", line 5, characters 25-34 *)
                 (acc intM_t_7 (shift t 1)) = 2 /\
                (* File "init.c", line 13, characters 25-51 *)
                ((acc intM_b_2 (acc b_s_9 s)) = 1 /\
                (acc intM_b_2 (shift (acc b_s_9 s) 2)) = 4)) /\
                (valid_range alloc t 0 2) /\ (valid alloc s) /\
                (constant_x x) /\
                (constant_s b_s_9 a_s_9 intM_b_2 s alloc) /\
                (valid1 b_s_9) /\ (valid1_range b_s_9 3)),
  forall (result: ((pointer) t_7)),
  forall (HW_2: result = (shift t 1)),
  forall (result0: Z),
  forall (HW_3: result0 = (acc intM_t_7 result)),
  forall (result1: ((pointer) b_2)),
  forall (HW_4: result1 = (acc b_s_9 s)),
  forall (result2: Z),
  forall (HW_5: result2 = (acc intM_b_2 result1)),
  forall (result3: ((pointer) b_2)),
  forall (HW_6: result3 = (acc b_s_9 s)),
  forall (result4: ((pointer) b_2)),
  forall (HW_7: result4 = (shift result3 2)),
  forall (result5: Z),
  forall (HW_8: result5 = (acc intM_b_2 result4)),
  (* File "init.c", line 15, characters 13-25 *)
  (result0 + result2 + result5) = 7.
Proof.
intuition.
subst;auto.
rewrite H0.
rewrite H4.
rewrite H1.
auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (a_s_9: ((memory) Z s_9)),
  forall (alloc: alloc_table),
  forall (b_s_9: ((memory) ((pointer) b_2) s_9)),
  forall (intM_b_2: ((memory) Z b_2)),
  forall (intM_t_7: ((memory) Z t_7)),
  forall (s: ((pointer) s_9)),
  forall (t: ((pointer) t_7)),
  forall (x: Z),
  forall (HW_1: ((* File "init.c", line 5, characters 25-34 *)
                 (acc intM_t_7 (shift t 1)) = 2 /\
                (* File "init.c", line 13, characters 25-51 *)
                ((acc intM_b_2 (acc b_s_9 s)) = 1 /\
                (acc intM_b_2 (shift (acc b_s_9 s) 2)) = 4)) /\
                (valid_range alloc t 0 2) /\ (valid alloc s) /\
                (constant_x x) /\
                (constant_s b_s_9 a_s_9 intM_b_2 s alloc) /\
                (valid1 b_s_9) /\ (valid1_range b_s_9 3)),
  forall (result: ((pointer) t_7)),
  forall (HW_2: result = (shift t 1)),
  forall (result0: Z),
  forall (HW_3: result0 = (acc intM_t_7 result)),
  forall (result1: ((pointer) b_2)),
  forall (HW_4: result1 = (acc b_s_9 s)),
  forall (result2: Z),
  forall (HW_5: result2 = (acc intM_b_2 result1)),
  forall (result3: ((pointer) b_2)),
  forall (HW_6: result3 = (acc b_s_9 s)),
  forall (result4: ((pointer) b_2)),
  forall (HW_7: result4 = (shift result3 2)),
  forall (result5: Z),
  forall (HW_8: result5 = (acc intM_b_2 result4)),
  (* File "init.c", line 5, characters 25-34 *) (acc intM_t_7 (shift t 1)) =
  2.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_3 : 
  forall (a_s_9: ((memory) Z s_9)),
  forall (alloc: alloc_table),
  forall (b_s_9: ((memory) ((pointer) b_2) s_9)),
  forall (intM_b_2: ((memory) Z b_2)),
  forall (intM_t_7: ((memory) Z t_7)),
  forall (s: ((pointer) s_9)),
  forall (t: ((pointer) t_7)),
  forall (x: Z),
  forall (HW_1: ((* File "init.c", line 5, characters 25-34 *)
                 (acc intM_t_7 (shift t 1)) = 2 /\
                (* File "init.c", line 13, characters 25-51 *)
                ((acc intM_b_2 (acc b_s_9 s)) = 1 /\
                (acc intM_b_2 (shift (acc b_s_9 s) 2)) = 4)) /\
                (valid_range alloc t 0 2) /\ (valid alloc s) /\
                (constant_x x) /\
                (constant_s b_s_9 a_s_9 intM_b_2 s alloc) /\
                (valid1 b_s_9) /\ (valid1_range b_s_9 3)),
  forall (result: ((pointer) t_7)),
  forall (HW_2: result = (shift t 1)),
  forall (result0: Z),
  forall (HW_3: result0 = (acc intM_t_7 result)),
  forall (result1: ((pointer) b_2)),
  forall (HW_4: result1 = (acc b_s_9 s)),
  forall (result2: Z),
  forall (HW_5: result2 = (acc intM_b_2 result1)),
  forall (result3: ((pointer) b_2)),
  forall (HW_6: result3 = (acc b_s_9 s)),
  forall (result4: ((pointer) b_2)),
  forall (HW_7: result4 = (shift result3 2)),
  forall (result5: Z),
  forall (HW_8: result5 = (acc intM_b_2 result4)),
  (acc intM_b_2 (acc b_s_9 s)) = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_4 : 
  forall (a_s_9: ((memory) Z s_9)),
  forall (alloc: alloc_table),
  forall (b_s_9: ((memory) ((pointer) b_2) s_9)),
  forall (intM_b_2: ((memory) Z b_2)),
  forall (intM_t_7: ((memory) Z t_7)),
  forall (s: ((pointer) s_9)),
  forall (t: ((pointer) t_7)),
  forall (x: Z),
  forall (HW_1: ((* File "init.c", line 5, characters 25-34 *)
                 (acc intM_t_7 (shift t 1)) = 2 /\
                (* File "init.c", line 13, characters 25-51 *)
                ((acc intM_b_2 (acc b_s_9 s)) = 1 /\
                (acc intM_b_2 (shift (acc b_s_9 s) 2)) = 4)) /\
                (valid_range alloc t 0 2) /\ (valid alloc s) /\
                (constant_x x) /\
                (constant_s b_s_9 a_s_9 intM_b_2 s alloc) /\
                (valid1 b_s_9) /\ (valid1_range b_s_9 3)),
  forall (result: ((pointer) t_7)),
  forall (HW_2: result = (shift t 1)),
  forall (result0: Z),
  forall (HW_3: result0 = (acc intM_t_7 result)),
  forall (result1: ((pointer) b_2)),
  forall (HW_4: result1 = (acc b_s_9 s)),
  forall (result2: Z),
  forall (HW_5: result2 = (acc intM_b_2 result1)),
  forall (result3: ((pointer) b_2)),
  forall (HW_6: result3 = (acc b_s_9 s)),
  forall (result4: ((pointer) b_2)),
  forall (HW_7: result4 = (shift result3 2)),
  forall (result5: Z),
  forall (HW_8: result5 = (acc intM_b_2 result4)),
  (acc intM_b_2 (shift (acc b_s_9 s) 2)) = 4.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (a_s_9: ((memory) Z s_9)),
  forall (alloc: alloc_table),
  forall (b_s_9: ((memory) ((pointer) b_2) s_9)),
  forall (intM_b_2: ((memory) Z b_2)),
  forall (s: ((pointer) s_9)),
  forall (t: ((pointer) t_7)),
  forall (x: Z),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid alloc s) /\
                (constant_x x) /\ (constant_s b_s_9 a_s_9 intM_b_2 s alloc)),
  2 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (A883:Set),
  forall (a_s_9: ((memory) Z s_9)),
  forall (alloc: alloc_table),
  forall (b_s_9: ((memory) ((pointer) b_2) s_9)),
  forall (intM_b_2: ((memory) Z b_2)),
  forall (intM_t_5: ((memory) Z A883)),
  forall (s: ((pointer) s_9)),
  forall (t: ((pointer) t_7)),
  forall (x: Z),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid alloc s) /\
                (constant_x x) /\ (constant_s b_s_9 a_s_9 intM_b_2 s alloc)),
  forall (HW_2: 2 >= 1),
  forall (result: ((pointer) A883)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 2 /\
                (valid_range alloc0 result 0 (2 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (intM_t_5_0: ((memory) Z A883)),
  forall (HW_4: intM_t_5_0 = (upd intM_t_5 result 4)),
  forall (result0: ((pointer) A883)),
  forall (HW_5: result0 = (shift result 1)),
  forall (intM_t_5_1: ((memory) Z A883)),
  forall (HW_6: intM_t_5_1 = (upd intM_t_5_0 result0 5)),
  forall (result1: Z),
  forall (HW_7: result1 = (acc intM_t_5_1 result)),
  result1 = 4.
Proof.
intuition.
subst;auto.
rewrite acc_upd_neq;auto.
rewrite acc_upd_eq;auto.
replace (shift result 1 <> result) with (shift result 1 <> shift result 0).
apply neq_offset_neq_shift.
omega.
rewrite shift_zero.
auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_1 : 
  forall (a_s_9: ((memory) Z s_9)),
  forall (alloc: alloc_table),
  forall (b_s_9: ((memory) ((pointer) b_2) s_9)),
  forall (intM_b_2: ((memory) Z b_2)),
  forall (s: ((pointer) s_9)),
  forall (t: ((pointer) t_7)),
  forall (x: Z),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid alloc s) /\
                (constant_x x) /\ (constant_s b_s_9 a_s_9 intM_b_2 s alloc)),
  3 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_2 : 
  forall (A884:Set),
  forall (a_s_9: ((memory) Z s_9)),
  forall (alloc: alloc_table),
  forall (b_s_9: ((memory) ((pointer) b_2) s_9)),
  forall (intM_b_2: ((memory) Z b_2)),
  forall (intM_u_6: ((memory) Z A884)),
  forall (s: ((pointer) s_9)),
  forall (t: ((pointer) t_7)),
  forall (x: Z),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid alloc s) /\
                (constant_x x) /\ (constant_s b_s_9 a_s_9 intM_b_2 s alloc)),
  forall (HW_2: 3 >= 1),
  forall (result: ((pointer) A884)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 3 /\
                (valid_range alloc0 result 0 (3 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (intM_u_6_0: ((memory) Z A884)),
  forall (HW_4: intM_u_6_0 = (upd intM_u_6 result 3)),
  forall (result0: ((pointer) A884)),
  forall (HW_5: result0 = (shift result 1)),
  forall (intM_u_6_1: ((memory) Z A884)),
  forall (HW_6: intM_u_6_1 = (upd intM_u_6_0 result0 4)),
  forall (result1: ((pointer) A884)),
  forall (HW_7: result1 = (shift result 2)),
  forall (intM_u_6_2: ((memory) Z A884)),
  forall (HW_8: intM_u_6_2 = (upd intM_u_6_1 result1 5)),
  forall (result2: Z),
  forall (HW_9: result2 = (acc intM_u_6_2 result)),
  forall (result3: ((pointer) A884)),
  forall (HW_10: result3 = (shift result 1)),
  forall (result4: Z),
  forall (HW_11: result4 = (acc intM_u_6_2 result3)),
  forall (result5: ((pointer) A884)),
  forall (HW_12: result5 = (shift result 2)),
  forall (result6: Z),
  forall (HW_13: result6 = (acc intM_u_6_2 result5)),
  (result2 + result4 + result6) = 12.
Proof.
intuition;subst;auto.
rewrite acc_upd_neq;auto.
rewrite acc_upd_neq;auto.
rewrite acc_upd_eq;auto.
rewrite acc_upd_neq;auto.
rewrite acc_upd_eq;auto.
rewrite acc_upd_eq;auto.
apply neq_offset_neq_shift;omega.
replace (shift result 1 <> result) with (shift result 1 <> shift result 0).
apply neq_offset_neq_shift;omega.
rewrite shift_zero;auto.
replace (shift result 2 <> result) with (shift result 2 <> shift result 0).
apply neq_offset_neq_shift;omega.
rewrite shift_zero;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma invariants_initially_established_impl_po_1 : 
  forall (a_s_9: ((memory) Z s_9)),
  forall (alloc: alloc_table),
  forall (b_s_9: ((memory) ((pointer) b_2) s_9)),
  forall (intM_b_2: ((memory) Z b_2)),
  forall (intM_t_7: ((memory) Z t_7)),
  forall (s: ((pointer) s_9)),
  forall (t: ((pointer) t_7)),
  forall (x: Z),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid alloc s) /\
                (constant_x x) /\
                (constant_s b_s_9 a_s_9 intM_b_2 s alloc) /\
                (valid1 b_s_9) /\ (valid1_range b_s_9 3)),
  forall (x0: Z),
  forall (HW_2: x0 = 45),
  forall (intM_t_7_0: ((memory) Z t_7)),
  forall (HW_3: intM_t_7_0 = (upd intM_t_7 t 1)),
  forall (result: ((pointer) t_7)),
  forall (HW_4: result = (shift t 1)),
  forall (intM_t_7_1: ((memory) Z t_7)),
  forall (HW_5: intM_t_7_1 = (upd intM_t_7_0 result 2)),
  forall (result0: ((pointer) t_7)),
  forall (HW_6: result0 = (shift t 2)),
  forall (intM_t_7_2: ((memory) Z t_7)),
  forall (HW_7: intM_t_7_2 = (upd intM_t_7_1 result0 3)),
  forall (a_s_9_0: ((memory) Z s_9)),
  forall (HW_8: a_s_9_0 = (upd a_s_9 s 1)),
  forall (result1: ((pointer) b_2)),
  forall (HW_9: result1 = (acc b_s_9 s)),
  forall (intM_b_2_0: ((memory) Z b_2)),
  forall (HW_10: intM_b_2_0 = (upd intM_b_2 result1 1)),
  forall (result2: ((pointer) b_2)),
  forall (HW_11: result2 = (acc b_s_9 s)),
  forall (result3: ((pointer) b_2)),
  forall (HW_12: result3 = (shift result2 1)),
  forall (intM_b_2_1: ((memory) Z b_2)),
  forall (HW_13: intM_b_2_1 = (upd intM_b_2_0 result3 3)),
  forall (result4: ((pointer) b_2)),
  forall (HW_14: result4 = (acc b_s_9 s)),
  forall (result5: ((pointer) b_2)),
  forall (HW_15: result5 = (shift result4 2)),
  forall (intM_b_2_2: ((memory) Z b_2)),
  forall (HW_16: intM_b_2_2 = (upd intM_b_2_1 result5 4)),
  (acc intM_t_7_2 (shift t 1)) = 2.
Proof.
intuition;subst;auto.
rewrite acc_upd_neq.
rewrite acc_upd_eq;auto.
apply neq_offset_neq_shift;omega.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma invariants_initially_established_impl_po_2 : 
  forall (a_s_9: ((memory) Z s_9)),
  forall (alloc: alloc_table),
  forall (b_s_9: ((memory) ((pointer) b_2) s_9)),
  forall (intM_b_2: ((memory) Z b_2)),
  forall (intM_t_7: ((memory) Z t_7)),
  forall (s: ((pointer) s_9)),
  forall (t: ((pointer) t_7)),
  forall (x: Z),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid alloc s) /\
                (constant_x x) /\
                (constant_s b_s_9 a_s_9 intM_b_2 s alloc) /\
                (valid1 b_s_9) /\ (valid1_range b_s_9 3)),
  forall (x0: Z),
  forall (HW_2: x0 = 45),
  forall (intM_t_7_0: ((memory) Z t_7)),
  forall (HW_3: intM_t_7_0 = (upd intM_t_7 t 1)),
  forall (result: ((pointer) t_7)),
  forall (HW_4: result = (shift t 1)),
  forall (intM_t_7_1: ((memory) Z t_7)),
  forall (HW_5: intM_t_7_1 = (upd intM_t_7_0 result 2)),
  forall (result0: ((pointer) t_7)),
  forall (HW_6: result0 = (shift t 2)),
  forall (intM_t_7_2: ((memory) Z t_7)),
  forall (HW_7: intM_t_7_2 = (upd intM_t_7_1 result0 3)),
  forall (a_s_9_0: ((memory) Z s_9)),
  forall (HW_8: a_s_9_0 = (upd a_s_9 s 1)),
  forall (result1: ((pointer) b_2)),
  forall (HW_9: result1 = (acc b_s_9 s)),
  forall (intM_b_2_0: ((memory) Z b_2)),
  forall (HW_10: intM_b_2_0 = (upd intM_b_2 result1 1)),
  forall (result2: ((pointer) b_2)),
  forall (HW_11: result2 = (acc b_s_9 s)),
  forall (result3: ((pointer) b_2)),
  forall (HW_12: result3 = (shift result2 1)),
  forall (intM_b_2_1: ((memory) Z b_2)),
  forall (HW_13: intM_b_2_1 = (upd intM_b_2_0 result3 3)),
  forall (result4: ((pointer) b_2)),
  forall (HW_14: result4 = (acc b_s_9 s)),
  forall (result5: ((pointer) b_2)),
  forall (HW_15: result5 = (shift result4 2)),
  forall (intM_b_2_2: ((memory) Z b_2)),
  forall (HW_16: intM_b_2_2 = (upd intM_b_2_1 result5 4)),
  (acc intM_b_2_2 (acc b_s_9 s)) = 1.
Proof.
intuition.
subst;auto.
rewrite acc_upd_neq.
rewrite acc_upd_neq.
rewrite acc_upd_eq;auto.
replace (shift (s # b_s_9) 1 <> s # b_s_9) with (shift (s # b_s_9) 1 <> shift (s # b_s_9) 0).
apply neq_offset_neq_shift;omega.
rewrite shift_zero;auto.
replace (shift (s # b_s_9) 2 <> s # b_s_9) with (shift (s # b_s_9) 2 <> shift (s # b_s_9) 0).
apply neq_offset_neq_shift;omega.
rewrite shift_zero;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma invariants_initially_established_impl_po_3 : 
  forall (a_s_9: ((memory) Z s_9)),
  forall (alloc: alloc_table),
  forall (b_s_9: ((memory) ((pointer) b_2) s_9)),
  forall (intM_b_2: ((memory) Z b_2)),
  forall (intM_t_7: ((memory) Z t_7)),
  forall (s: ((pointer) s_9)),
  forall (t: ((pointer) t_7)),
  forall (x: Z),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid alloc s) /\
                (constant_x x) /\
                (constant_s b_s_9 a_s_9 intM_b_2 s alloc) /\
                (valid1 b_s_9) /\ (valid1_range b_s_9 3)),
  forall (x0: Z),
  forall (HW_2: x0 = 45),
  forall (intM_t_7_0: ((memory) Z t_7)),
  forall (HW_3: intM_t_7_0 = (upd intM_t_7 t 1)),
  forall (result: ((pointer) t_7)),
  forall (HW_4: result = (shift t 1)),
  forall (intM_t_7_1: ((memory) Z t_7)),
  forall (HW_5: intM_t_7_1 = (upd intM_t_7_0 result 2)),
  forall (result0: ((pointer) t_7)),
  forall (HW_6: result0 = (shift t 2)),
  forall (intM_t_7_2: ((memory) Z t_7)),
  forall (HW_7: intM_t_7_2 = (upd intM_t_7_1 result0 3)),
  forall (a_s_9_0: ((memory) Z s_9)),
  forall (HW_8: a_s_9_0 = (upd a_s_9 s 1)),
  forall (result1: ((pointer) b_2)),
  forall (HW_9: result1 = (acc b_s_9 s)),
  forall (intM_b_2_0: ((memory) Z b_2)),
  forall (HW_10: intM_b_2_0 = (upd intM_b_2 result1 1)),
  forall (result2: ((pointer) b_2)),
  forall (HW_11: result2 = (acc b_s_9 s)),
  forall (result3: ((pointer) b_2)),
  forall (HW_12: result3 = (shift result2 1)),
  forall (intM_b_2_1: ((memory) Z b_2)),
  forall (HW_13: intM_b_2_1 = (upd intM_b_2_0 result3 3)),
  forall (result4: ((pointer) b_2)),
  forall (HW_14: result4 = (acc b_s_9 s)),
  forall (result5: ((pointer) b_2)),
  forall (HW_15: result5 = (shift result4 2)),
  forall (intM_b_2_2: ((memory) Z b_2)),
  forall (HW_16: intM_b_2_2 = (upd intM_b_2_1 result5 4)),
  (acc intM_b_2_2 (shift (acc b_s_9 s) 2)) = 4.
Proof.
intuition.
subst;caduceus.
Save.

