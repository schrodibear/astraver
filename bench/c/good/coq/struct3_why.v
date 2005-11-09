(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export struct3_spec_why.

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
  (valid alloc0 result).
Proof.
intuition; subst; auto;
caduceus;
red;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (x_Z3: ((memory) Z Z3)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z3)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (x_Z3_0: ((memory) Z Z3)),
  forall (HW_4: x_Z3_0 = (upd x_Z3 result 1)),
  (valid alloc0 result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (x_Z3: ((memory) Z Z3)),
  forall (y_Z3: ((memory) Z Z3)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z3)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (x_Z3_0: ((memory) Z Z3)),
  forall (HW_4: x_Z3_0 = (upd x_Z3 result 1)),
  forall (HW_5: (valid alloc0 result)),
  forall (y_Z3_0: ((memory) Z Z3)),
  forall (HW_6: y_Z3_0 = (upd y_Z3 result 2)),
  (valid alloc0 result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (x_Z3: ((memory) Z Z3)),
  forall (y_Z3: ((memory) Z Z3)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z3)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (x_Z3_0: ((memory) Z Z3)),
  forall (HW_4: x_Z3_0 = (upd x_Z3 result 1)),
  forall (HW_5: (valid alloc0 result)),
  forall (y_Z3_0: ((memory) Z Z3)),
  forall (HW_6: y_Z3_0 = (upd y_Z3 result 2)),
  forall (HW_7: (valid alloc0 result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc y_Z3_0 result)),
  (* File "struct3.c", line 4, characters 13-25 *) result0 = 2.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  1 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z5)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  (valid alloc0 result).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (z_Z5: ((memory) Z Z5)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z5)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (z_Z5_0: ((memory) Z Z5)),
  forall (HW_4: z_Z5_0 = (upd z_Z5 result 1)),
  (valid alloc0 result).
Proof.
intuition; subst; auto; caduceus.
Save.
(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (s_Z5: ((memory) ((pointer) Z1) Z5)),
  forall (z_Z5: ((memory) Z Z5)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z5)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (z_Z5_0: ((memory) Z Z5)),
  forall (HW_4: z_Z5_0 = (upd z_Z5 result 1)),
  forall (HW_5: (valid alloc0 result)),
  forall (result0: ((pointer) Z1)),
  forall (HW_6: result0 = (acc s_Z5 result)),
  (valid alloc0 result0).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (s_Z5: ((memory) ((pointer) Z1) Z5)),
  forall (x_Z1: ((memory) Z Z1)),
  forall (z_Z5: ((memory) Z Z5)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z5)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (z_Z5_0: ((memory) Z Z5)),
  forall (HW_4: z_Z5_0 = (upd z_Z5 result 1)),
  forall (HW_5: (valid alloc0 result)),
  forall (result0: ((pointer) Z1)),
  forall (HW_6: result0 = (acc s_Z5 result)),
  forall (HW_7: (valid alloc0 result0)),
  forall (x_Z1_0: ((memory) Z Z1)),
  forall (HW_8: x_Z1_0 = (upd x_Z1 result0 2)),
  (valid alloc0 result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_6 : 
  forall (alloc: alloc_table),
  forall (s_Z5: ((memory) ((pointer) Z1) Z5)),
  forall (x_Z1: ((memory) Z Z1)),
  forall (z_Z5: ((memory) Z Z5)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z5)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (z_Z5_0: ((memory) Z Z5)),
  forall (HW_4: z_Z5_0 = (upd z_Z5 result 1)),
  forall (HW_5: (valid alloc0 result)),
  forall (result0: ((pointer) Z1)),
  forall (HW_6: result0 = (acc s_Z5 result)),
  forall (HW_7: (valid alloc0 result0)),
  forall (x_Z1_0: ((memory) Z Z1)),
  forall (HW_8: x_Z1_0 = (upd x_Z1 result0 2)),
  forall (HW_9: (valid alloc0 result)),
  forall (result1: ((pointer) Z1)),
  forall (HW_10: result1 = (acc s_Z5 result)),
  (valid alloc0 result1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_7 : 
  forall (alloc: alloc_table),
  forall (s_Z5: ((memory) ((pointer) Z1) Z5)),
  forall (x_Z1: ((memory) Z Z1)),
  forall (y_Z1: ((memory) Z Z1)),
  forall (z_Z5: ((memory) Z Z5)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z5)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (z_Z5_0: ((memory) Z Z5)),
  forall (HW_4: z_Z5_0 = (upd z_Z5 result 1)),
  forall (HW_5: (valid alloc0 result)),
  forall (result0: ((pointer) Z1)),
  forall (HW_6: result0 = (acc s_Z5 result)),
  forall (HW_7: (valid alloc0 result0)),
  forall (x_Z1_0: ((memory) Z Z1)),
  forall (HW_8: x_Z1_0 = (upd x_Z1 result0 2)),
  forall (HW_9: (valid alloc0 result)),
  forall (result1: ((pointer) Z1)),
  forall (HW_10: result1 = (acc s_Z5 result)),
  forall (HW_11: (valid alloc0 result1)),
  forall (y_Z1_0: ((memory) Z Z1)),
  forall (HW_12: y_Z1_0 = (upd y_Z1 result1 3)),
  (valid alloc0 result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_8 : 
  forall (alloc: alloc_table),
  forall (s_Z5: ((memory) ((pointer) Z1) Z5)),
  forall (x_Z1: ((memory) Z Z1)),
  forall (y_Z1: ((memory) Z Z1)),
  forall (z_Z5: ((memory) Z Z5)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z5)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (z_Z5_0: ((memory) Z Z5)),
  forall (HW_4: z_Z5_0 = (upd z_Z5 result 1)),
  forall (HW_5: (valid alloc0 result)),
  forall (result0: ((pointer) Z1)),
  forall (HW_6: result0 = (acc s_Z5 result)),
  forall (HW_7: (valid alloc0 result0)),
  forall (x_Z1_0: ((memory) Z Z1)),
  forall (HW_8: x_Z1_0 = (upd x_Z1 result0 2)),
  forall (HW_9: (valid alloc0 result)),
  forall (result1: ((pointer) Z1)),
  forall (HW_10: result1 = (acc s_Z5 result)),
  forall (HW_11: (valid alloc0 result1)),
  forall (y_Z1_0: ((memory) Z Z1)),
  forall (HW_12: y_Z1_0 = (upd y_Z1 result1 3)),
  forall (HW_13: (valid alloc0 result)),
  forall (result2: ((pointer) Z1)),
  forall (HW_14: result2 = (acc s_Z5 result)),
  (valid alloc0 result2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_9 : 
  forall (alloc: alloc_table),
  forall (s_Z5: ((memory) ((pointer) Z1) Z5)),
  forall (x_Z1: ((memory) Z Z1)),
  forall (y_Z1: ((memory) Z Z1)),
  forall (z_Z5: ((memory) Z Z5)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z5)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (z_Z5_0: ((memory) Z Z5)),
  forall (HW_4: z_Z5_0 = (upd z_Z5 result 1)),
  forall (HW_5: (valid alloc0 result)),
  forall (result0: ((pointer) Z1)),
  forall (HW_6: result0 = (acc s_Z5 result)),
  forall (HW_7: (valid alloc0 result0)),
  forall (x_Z1_0: ((memory) Z Z1)),
  forall (HW_8: x_Z1_0 = (upd x_Z1 result0 2)),
  forall (HW_9: (valid alloc0 result)),
  forall (result1: ((pointer) Z1)),
  forall (HW_10: result1 = (acc s_Z5 result)),
  forall (HW_11: (valid alloc0 result1)),
  forall (y_Z1_0: ((memory) Z Z1)),
  forall (HW_12: y_Z1_0 = (upd y_Z1 result1 3)),
  forall (HW_13: (valid alloc0 result)),
  forall (result2: ((pointer) Z1)),
  forall (HW_14: result2 = (acc s_Z5 result)),
  forall (HW_15: (valid alloc0 result2)),
  forall (result3: Z),
  forall (HW_16: result3 = (acc y_Z1_0 result2)),
  (* File "struct3.c", line 13, characters 13-25 *) result3 = 3.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

