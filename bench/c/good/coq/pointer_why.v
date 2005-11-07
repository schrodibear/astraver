(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma array1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (int_Z14: ((memory) Z Z14)),
  forall (t: ((pointer) Z14)),
  forall (HW_1: (* File \"pointer.c\", line 42, characters 14-31:\n *)
                (valid_index alloc t 2) /\ (valid_range alloc t 0 4)),
  forall (result: ((pointer) Z14)),
  forall (HW_3: result = (shift t 2)),
  forall (p: ((pointer) Z14)),
  forall (HW_4: p = result),
  forall (result0: ((pointer) Z14)),
  forall (HW_5: result0 = (shift p 1)),
  forall (p0: ((pointer) Z14)),
  forall (HW_6: p0 = result0),
  forall (int_Z14_0: ((memory) Z Z14)),
  forall (HW_7: int_Z14_0 = (upd int_Z14 p 1)),
  (* File \"pointer.c\", line 42, characters 40-52:\n *) 1 = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma array1_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (t: ((pointer) Z14)),
  forall (HW_1: (* File \"pointer.c\", line 42, characters 14-31:\n *)
                (valid_index alloc t 2) /\ (valid_range alloc t 0 4)),
  forall (result: ((pointer) Z14)),
  forall (HW_3: result = (shift t 2)),
  forall (p: ((pointer) Z14)),
  forall (HW_4: p = result),
  forall (result0: ((pointer) Z14)),
  forall (HW_5: result0 = (shift p 1)),
  forall (p0: ((pointer) Z14)),
  forall (HW_6: p0 = result0),
  (valid alloc p).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_1 : 
  forall (x: ((pointer) Z10)),
  forall (alloc: alloc_table),
  forall (int_Z10: ((memory) Z Z10)),
  forall (HW_1: (* File \"pointer.c\", line 12, characters 14-23:\n *)
                (valid alloc x)),
  forall (int_Z10_0: ((memory) Z Z10)),
  forall (HW_2: int_Z10_0 = (upd int_Z10 x 0)),
  forall (result: Z),
  forall (HW_3: result = (acc int_Z10_0 x)),
  forall (int_Z10_1: ((memory) Z Z10)),
  forall (HW_4: int_Z10_1 = (upd int_Z10_0 x (result + 1))),
  (* File \"pointer.c\", line 13, characters 13-36:\n *) ((acc int_Z10_1 x) =
  1 /\ (result + 1) = 1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_2 : 
  forall (x: ((pointer) Z10)),
  forall (alloc: alloc_table),
  forall (int_Z10: ((memory) Z Z10)),
  forall (HW_1: (* File \"pointer.c\", line 12, characters 14-23:\n *)
                (valid alloc x)),
  forall (int_Z10_0: ((memory) Z Z10)),
  forall (HW_2: int_Z10_0 = (upd int_Z10 x 0)),
  forall (result: Z),
  forall (HW_3: result = (acc int_Z10_0 x)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_3 : 
  forall (x: ((pointer) Z10)),
  forall (alloc: alloc_table),
  forall (int_Z10: ((memory) Z Z10)),
  forall (HW_1: (* File \"pointer.c\", line 12, characters 14-23:\n *)
                (valid alloc x)),
  forall (int_Z10_0: ((memory) Z Z10)),
  forall (HW_2: int_Z10_0 = (upd int_Z10 x 0)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_4 : 
  forall (x: ((pointer) Z10)),
  forall (alloc: alloc_table),
  forall (HW_1: (* File \"pointer.c\", line 12, characters 14-23:\n *)
                (valid alloc x)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (x: ((pointer) Z13)),
  forall (alloc: alloc_table),
  forall (int_Z13: ((memory) Z Z13)),
  forall (HW_1: (* File \"pointer.c\", line 4, characters 14-23:\n *)
                (valid alloc x)),
  forall (int_Z13_0: ((memory) Z Z13)),
  forall (HW_2: int_Z13_0 = (upd int_Z13 x 0)),
  forall (result: Z),
  forall (HW_3: result = (acc int_Z13_0 x)),
  forall (int_Z13_1: ((memory) Z Z13)),
  forall (HW_4: int_Z13_1 = (upd int_Z13_0 x (1 + result))),
  (* File \"pointer.c\", line 6, characters 13-36:\n *) ((acc int_Z13_1 x) =
  1 /\ result = 0) /\
  (not_assigns alloc int_Z13 int_Z13_1 (pset_singleton x)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (x: ((pointer) Z13)),
  forall (alloc: alloc_table),
  forall (int_Z13: ((memory) Z Z13)),
  forall (HW_1: (* File \"pointer.c\", line 4, characters 14-23:\n *)
                (valid alloc x)),
  forall (int_Z13_0: ((memory) Z Z13)),
  forall (HW_2: int_Z13_0 = (upd int_Z13 x 0)),
  forall (result: Z),
  forall (HW_3: result = (acc int_Z13_0 x)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_3 : 
  forall (x: ((pointer) Z13)),
  forall (alloc: alloc_table),
  forall (int_Z13: ((memory) Z Z13)),
  forall (HW_1: (* File \"pointer.c\", line 4, characters 14-23:\n *)
                (valid alloc x)),
  forall (int_Z13_0: ((memory) Z Z13)),
  forall (HW_2: int_Z13_0 = (upd int_Z13 x 0)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_4 : 
  forall (x: ((pointer) Z13)),
  forall (alloc: alloc_table),
  forall (HW_1: (* File \"pointer.c\", line 4, characters 14-23:\n *)
                (valid alloc x)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (int_Z13: ((memory) Z Z13)),
  forall (r: ((pointer) Z13)),
  forall (HW_1: (* File \"pointer.c\", line 22, characters 14-23:\n *)
                (valid alloc r)),
  forall (result: Z),
  forall (int_Z13_0: ((memory) Z Z13)),
  forall (HW_2: (* File \"pointer.c\", line 6, characters 13-36:\n *)
                ((acc int_Z13_0 r) = 1 /\ result = 0) /\
                (not_assigns alloc int_Z13 int_Z13_0 (pset_singleton r))),
  (* File \"pointer.c\", line 23, characters 13-20:\n *) (acc int_Z13_0 r) =
  1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (r: ((pointer) Z13)),
  forall (HW_1: (* File \"pointer.c\", line 22, characters 14-23:\n *)
                (valid alloc r)),
  (* File \"pointer.c\", line 4, characters 14-23:\n *) (valid alloc r).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (int_Z13: ((memory) Z Z13)),
  forall (result: ((pointer) Z13)),
  forall (alloc0: alloc_table),
  forall (HW_1: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (int_Z13_0: ((memory) Z Z13)),
  forall (HW_2: int_Z13_0 = (upd int_Z13 result 0)),
  forall (result0: Z),
  forall (int_Z13_1: ((memory) Z Z13)),
  forall (HW_3: (* File \"pointer.c\", line 6, characters 13-36:\n *)
                ((acc int_Z13_1 result) = 1 /\ result0 = 0) /\
                (not_assigns alloc0 int_Z13_0 int_Z13_1
                 (pset_singleton result))),
  forall (result1: Z),
  forall (HW_4: result1 = (acc int_Z13_1 result)),
  (* File \"pointer.c\", line 36, characters 13-25:\n *)
  (result0 + result1) = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (int_Z13: ((memory) Z Z13)),
  forall (result: ((pointer) Z13)),
  forall (alloc0: alloc_table),
  forall (HW_1: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (int_Z13_0: ((memory) Z Z13)),
  forall (HW_2: int_Z13_0 = (upd int_Z13 result 0)),
  forall (result0: Z),
  forall (int_Z13_1: ((memory) Z Z13)),
  forall (HW_3: (* File \"pointer.c\", line 6, characters 13-36:\n *)
                ((acc int_Z13_1 result) = 1 /\ result0 = 0) /\
                (not_assigns alloc0 int_Z13_0 int_Z13_1
                 (pset_singleton result))),
  (valid alloc0 result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (int_Z13: ((memory) Z Z13)),
  forall (result: ((pointer) Z13)),
  forall (alloc0: alloc_table),
  forall (HW_1: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (int_Z13_0: ((memory) Z Z13)),
  forall (HW_2: int_Z13_0 = (upd int_Z13 result 0)),
  (* File \"pointer.c\", line 4, characters 14-23:\n *) (valid alloc0 result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (result: ((pointer) Z13)),
  forall (alloc0: alloc_table),
  forall (HW_1: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  (valid alloc0 result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_5 : 
  1 >= 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (int_Z8: ((memory) Z Z8)),
  forall (s: ((pointer) Z16)),
  forall (x_Z16: ((memory) ((pointer) Z8) Z16)),
  forall (y_Z16: ((memory) Z Z16)),
  forall (HW_1: (* File \"pointer.c\", line 53, characters 14-23:\n *)
                (valid alloc s) /\ (valid_range alloc s 0 0)),
  forall (result: ((pointer) Z8)),
  forall (HW_2: result = (acc x_Z16 s)),
  forall (int_Z8_0: ((memory) Z Z8)),
  forall (HW_3: int_Z8_0 = (upd int_Z8 result 1)),
  forall (y_Z16_0: ((memory) Z Z16)),
  forall (HW_4: y_Z16_0 = (upd y_Z16 s 2)),
  forall (result0: Z),
  forall (HW_5: result0 = (acc int_Z8_0 result)),
  (* File \"pointer.c\", line 53, characters 33-45:\n *) result0 >= 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (int_Z8: ((memory) Z Z8)),
  forall (s: ((pointer) Z16)),
  forall (x_Z16: ((memory) ((pointer) Z8) Z16)),
  forall (y_Z16: ((memory) Z Z16)),
  forall (HW_1: (* File \"pointer.c\", line 53, characters 14-23:\n *)
                (valid alloc s) /\ (valid_range alloc s 0 0)),
  forall (result: ((pointer) Z8)),
  forall (HW_2: result = (acc x_Z16 s)),
  forall (int_Z8_0: ((memory) Z Z8)),
  forall (HW_3: int_Z8_0 = (upd int_Z8 result 1)),
  forall (y_Z16_0: ((memory) Z Z16)),
  forall (HW_4: y_Z16_0 = (upd y_Z16 s 2)),
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (int_Z8: ((memory) Z Z8)),
  forall (s: ((pointer) Z16)),
  forall (x_Z16: ((memory) ((pointer) Z8) Z16)),
  forall (HW_1: (* File \"pointer.c\", line 53, characters 14-23:\n *)
                (valid alloc s) /\ (valid_range alloc s 0 0)),
  forall (result: ((pointer) Z8)),
  forall (HW_2: result = (acc x_Z16 s)),
  forall (int_Z8_0: ((memory) Z Z8)),
  forall (HW_3: int_Z8_0 = (upd int_Z8 result 1)),
  (valid alloc s).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (s: ((pointer) Z16)),
  forall (x_Z16: ((memory) ((pointer) Z8) Z16)),
  forall (HW_1: (* File \"pointer.c\", line 53, characters 14-23:\n *)
                (valid alloc s) /\ (valid_range alloc s 0 0)),
  forall (result: ((pointer) Z8)),
  forall (HW_2: result = (acc x_Z16 s)),
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (s: ((pointer) Z16)),
  forall (HW_1: (* File \"pointer.c\", line 53, characters 14-23:\n *)
                (valid alloc s) /\ (valid_range alloc s 0 0)),
  (valid alloc s).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

