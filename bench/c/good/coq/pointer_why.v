(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma array1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (t: ((pointer) Z16)),
  forall (HW_1: (* File "pointer.c", line 42, characters 14-31 *)
                (valid_index alloc t 2) /\ (valid_range alloc t 0 4)),
  forall (result: ((pointer) Z16)),
  forall (HW_3: result = (shift t 2)),
  forall (p: ((pointer) Z16)),
  forall (HW_4: p = result),
  forall (result0: ((pointer) Z16)),
  forall (HW_5: result0 = (shift p 1)),
  forall (p0: ((pointer) Z16)),
  forall (HW_6: p0 = result0),
  (valid alloc p).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma array1_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (int_Z16: ((memory) Z Z16)),
  forall (t: ((pointer) Z16)),
  forall (HW_1: (* File "pointer.c", line 42, characters 14-31 *)
                (valid_index alloc t 2) /\ (valid_range alloc t 0 4)),
  forall (result: ((pointer) Z16)),
  forall (HW_3: result = (shift t 2)),
  forall (p: ((pointer) Z16)),
  forall (HW_4: p = result),
  forall (result0: ((pointer) Z16)),
  forall (HW_5: result0 = (shift p 1)),
  forall (p0: ((pointer) Z16)),
  forall (HW_6: p0 = result0),
  forall (HW_7: (valid alloc p)),
  forall (int_Z16_0: ((memory) Z Z16)),
  forall (HW_8: int_Z16_0 = (upd int_Z16 p 1)),
  (* File "pointer.c", line 42, characters 40-52 *) 1 = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_1 : 
  forall (x: ((pointer) Z12)),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "pointer.c", line 12, characters 14-23 *)
                (valid alloc x)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_2 : 
  forall (x: ((pointer) Z12)),
  forall (alloc: alloc_table),
  forall (int_Z12: ((memory) Z Z12)),
  forall (HW_1: (* File "pointer.c", line 12, characters 14-23 *)
                (valid alloc x)),
  forall (HW_2: (valid alloc x)),
  forall (int_Z12_0: ((memory) Z Z12)),
  forall (HW_3: int_Z12_0 = (upd int_Z12 x 0)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_3 : 
  forall (x: ((pointer) Z12)),
  forall (alloc: alloc_table),
  forall (int_Z12: ((memory) Z Z12)),
  forall (HW_1: (* File "pointer.c", line 12, characters 14-23 *)
                (valid alloc x)),
  forall (HW_2: (valid alloc x)),
  forall (int_Z12_0: ((memory) Z Z12)),
  forall (HW_3: int_Z12_0 = (upd int_Z12 x 0)),
  forall (HW_4: (valid alloc x)),
  forall (result: Z),
  forall (HW_5: result = (acc int_Z12_0 x)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_4 : 
  forall (x: ((pointer) Z12)),
  forall (alloc: alloc_table),
  forall (int_Z12: ((memory) Z Z12)),
  forall (HW_1: (* File "pointer.c", line 12, characters 14-23 *)
                (valid alloc x)),
  forall (HW_2: (valid alloc x)),
  forall (int_Z12_0: ((memory) Z Z12)),
  forall (HW_3: int_Z12_0 = (upd int_Z12 x 0)),
  forall (HW_4: (valid alloc x)),
  forall (result: Z),
  forall (HW_5: result = (acc int_Z12_0 x)),
  forall (HW_6: (valid alloc x)),
  forall (int_Z12_1: ((memory) Z Z12)),
  forall (HW_7: int_Z12_1 = (upd int_Z12_0 x (result + 1))),
  (* File "pointer.c", line 13, characters 13-36 *) ((acc int_Z12_1 x) = 1 /\
  (result + 1) = 1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (x: ((pointer) Z15)),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "pointer.c", line 4, characters 14-23 *)
                (valid alloc x)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (x: ((pointer) Z15)),
  forall (alloc: alloc_table),
  forall (int_Z15: ((memory) Z Z15)),
  forall (HW_1: (* File "pointer.c", line 4, characters 14-23 *)
                (valid alloc x)),
  forall (HW_2: (valid alloc x)),
  forall (int_Z15_0: ((memory) Z Z15)),
  forall (HW_3: int_Z15_0 = (upd int_Z15 x 0)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_3 : 
  forall (x: ((pointer) Z15)),
  forall (alloc: alloc_table),
  forall (int_Z15: ((memory) Z Z15)),
  forall (HW_1: (* File "pointer.c", line 4, characters 14-23 *)
                (valid alloc x)),
  forall (HW_2: (valid alloc x)),
  forall (int_Z15_0: ((memory) Z Z15)),
  forall (HW_3: int_Z15_0 = (upd int_Z15 x 0)),
  forall (HW_4: (valid alloc x)),
  forall (result: Z),
  forall (HW_5: result = (acc int_Z15_0 x)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_4 : 
  forall (x: ((pointer) Z15)),
  forall (alloc: alloc_table),
  forall (int_Z15: ((memory) Z Z15)),
  forall (HW_1: (* File "pointer.c", line 4, characters 14-23 *)
                (valid alloc x)),
  forall (HW_2: (valid alloc x)),
  forall (int_Z15_0: ((memory) Z Z15)),
  forall (HW_3: int_Z15_0 = (upd int_Z15 x 0)),
  forall (HW_4: (valid alloc x)),
  forall (result: Z),
  forall (HW_5: result = (acc int_Z15_0 x)),
  forall (HW_6: (valid alloc x)),
  forall (int_Z15_1: ((memory) Z Z15)),
  forall (HW_7: int_Z15_1 = (upd int_Z15_0 x (1 + result))),
  (* File "pointer.c", line 6, characters 13-36 *) ((acc int_Z15_1 x) = 1 /\
  result = 0) /\ (not_assigns alloc int_Z15 int_Z15_1 (pset_singleton x)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (r: ((pointer) Z15)),
  forall (HW_1: (* File "pointer.c", line 22, characters 14-23 *)
                (valid alloc r)),
  (* File "pointer.c", line 4, characters 14-23 *) (valid alloc r).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (int_Z15: ((memory) Z Z15)),
  forall (r: ((pointer) Z15)),
  forall (HW_1: (* File "pointer.c", line 22, characters 14-23 *)
                (valid alloc r)),
  forall (HW_2: (* File "pointer.c", line 4, characters 14-23 *)
                (valid alloc r)),
  forall (result: Z),
  forall (int_Z15_0: ((memory) Z Z15)),
  forall (HW_3: (* File "pointer.c", line 6, characters 13-36 *)
                ((acc int_Z15_0 r) = 1 /\ result = 0) /\
                (not_assigns alloc int_Z15 int_Z15_0 (pset_singleton r))),
  (* File "pointer.c", line 23, characters 13-20 *) (acc int_Z15_0 r) = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_1 : 
  1 >= 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z15)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  (valid alloc0 result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (int_Z15: ((memory) Z Z15)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z15)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (int_Z15_0: ((memory) Z Z15)),
  forall (HW_4: int_Z15_0 = (upd int_Z15 result 0)),
  (* File "pointer.c", line 4, characters 14-23 *) (valid alloc0 result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (int_Z15: ((memory) Z Z15)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z15)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (int_Z15_0: ((memory) Z Z15)),
  forall (HW_4: int_Z15_0 = (upd int_Z15 result 0)),
  forall (HW_5: (* File "pointer.c", line 4, characters 14-23 *)
                (valid alloc0 result)),
  forall (result0: Z),
  forall (int_Z15_1: ((memory) Z Z15)),
  forall (HW_6: (* File "pointer.c", line 6, characters 13-36 *)
                ((acc int_Z15_1 result) = 1 /\ result0 = 0) /\
                (not_assigns alloc0 int_Z15_0 int_Z15_1
                 (pset_singleton result))),
  (valid alloc0 result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (int_Z15: ((memory) Z Z15)),
  forall (HW_1: 1 >= 1),
  forall (result: ((pointer) Z15)),
  forall (alloc0: alloc_table),
  forall (HW_2: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_3: (valid alloc0 result)),
  forall (int_Z15_0: ((memory) Z Z15)),
  forall (HW_4: int_Z15_0 = (upd int_Z15 result 0)),
  forall (HW_5: (* File "pointer.c", line 4, characters 14-23 *)
                (valid alloc0 result)),
  forall (result0: Z),
  forall (int_Z15_1: ((memory) Z Z15)),
  forall (HW_6: (* File "pointer.c", line 6, characters 13-36 *)
                ((acc int_Z15_1 result) = 1 /\ result0 = 0) /\
                (not_assigns alloc0 int_Z15_0 int_Z15_1
                 (pset_singleton result))),
  forall (HW_7: (valid alloc0 result)),
  forall (result1: Z),
  forall (HW_8: result1 = (acc int_Z15_1 result)),
  (* File "pointer.c", line 36, characters 13-25 *) (result0 + result1) = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (s: ((pointer) Z18)),
  forall (HW_1: (* File "pointer.c", line 53, characters 14-23 *)
                (valid alloc s) /\ (valid_range alloc s 0 0)),
  (valid alloc s).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (s: ((pointer) Z18)),
  forall (x_Z18: ((memory) ((pointer) Z10) Z18)),
  forall (HW_1: (* File "pointer.c", line 53, characters 14-23 *)
                (valid alloc s) /\ (valid_range alloc s 0 0)),
  forall (HW_2: (valid alloc s)),
  forall (result: ((pointer) Z10)),
  forall (HW_3: result = (acc x_Z18 s)),
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (int_Z10: ((memory) Z Z10)),
  forall (s: ((pointer) Z18)),
  forall (x_Z18: ((memory) ((pointer) Z10) Z18)),
  forall (HW_1: (* File "pointer.c", line 53, characters 14-23 *)
                (valid alloc s) /\ (valid_range alloc s 0 0)),
  forall (HW_2: (valid alloc s)),
  forall (result: ((pointer) Z10)),
  forall (HW_3: result = (acc x_Z18 s)),
  forall (HW_4: (valid alloc result)),
  forall (int_Z10_0: ((memory) Z Z10)),
  forall (HW_5: int_Z10_0 = (upd int_Z10 result 1)),
  (valid alloc s).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (int_Z10: ((memory) Z Z10)),
  forall (s: ((pointer) Z18)),
  forall (x_Z18: ((memory) ((pointer) Z10) Z18)),
  forall (y_Z18: ((memory) Z Z18)),
  forall (HW_1: (* File "pointer.c", line 53, characters 14-23 *)
                (valid alloc s) /\ (valid_range alloc s 0 0)),
  forall (HW_2: (valid alloc s)),
  forall (result: ((pointer) Z10)),
  forall (HW_3: result = (acc x_Z18 s)),
  forall (HW_4: (valid alloc result)),
  forall (int_Z10_0: ((memory) Z Z10)),
  forall (HW_5: int_Z10_0 = (upd int_Z10 result 1)),
  forall (HW_6: (valid alloc s)),
  forall (y_Z18_0: ((memory) Z Z18)),
  forall (HW_7: y_Z18_0 = (upd y_Z18 s 2)),
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (int_Z10: ((memory) Z Z10)),
  forall (s: ((pointer) Z18)),
  forall (x_Z18: ((memory) ((pointer) Z10) Z18)),
  forall (y_Z18: ((memory) Z Z18)),
  forall (HW_1: (* File "pointer.c", line 53, characters 14-23 *)
                (valid alloc s) /\ (valid_range alloc s 0 0)),
  forall (HW_2: (valid alloc s)),
  forall (result: ((pointer) Z10)),
  forall (HW_3: result = (acc x_Z18 s)),
  forall (HW_4: (valid alloc result)),
  forall (int_Z10_0: ((memory) Z Z10)),
  forall (HW_5: int_Z10_0 = (upd int_Z10 result 1)),
  forall (HW_6: (valid alloc s)),
  forall (y_Z18_0: ((memory) Z Z18)),
  forall (HW_7: y_Z18_0 = (upd y_Z18 s 2)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc int_Z10_0 result)),
  (* File "pointer.c", line 53, characters 33-45 *) result0 >= 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

