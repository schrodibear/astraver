(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma array1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-27 *)
                (valid_index alloc t 2) /\ (valid_range alloc t 0 4)),
  forall (result: pointer),
  forall (HW_3: result = (shift t 2)),
  forall (p: pointer),
  forall (HW_4: p = result),
  forall (result0: pointer),
  forall (HW_5: result0 = (shift p 1)),
  forall (p0: pointer),
  forall (HW_6: p0 = result0),
  forall (intP0: ((memory) Z)),
  forall (HW_7: intP0 = (upd intP p 1)),
  (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 36-48 *)
  1 = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma array1_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (t: pointer),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-27 *)
                (valid_index alloc t 2) /\ (valid_range alloc t 0 4)),
  forall (result: pointer),
  forall (HW_3: result = (shift t 2)),
  forall (p: pointer),
  forall (HW_4: p = result),
  forall (result0: pointer),
  forall (HW_5: result0 = (shift p 1)),
  forall (p0: pointer),
  forall (HW_6: p0 = result0),
  (valid alloc p).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_1 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (HW_2: intP0 = (upd intP x 0)),
  forall (result: Z),
  forall (HW_3: result = (acc intP0 x)),
  forall (intP1: ((memory) Z)),
  forall (HW_4: intP1 = (upd intP0 x (result + 1))),
  (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 32-55 *)
  ((acc intP1 x) = 1 /\ (result + 1) = 1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_2 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (HW_2: intP0 = (upd intP x 0)),
  forall (result: Z),
  forall (HW_3: result = (acc intP0 x)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_3 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (HW_2: intP0 = (upd intP x 0)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_4 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc x)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (HW_2: intP0 = (upd intP x 0)),
  forall (result: Z),
  forall (HW_3: result = (acc intP0 x)),
  forall (intP1: ((memory) Z)),
  forall (HW_4: intP1 = (upd intP0 x (1 + result))),
  (* File \"pointer.c819618234.c\", line 0, characters 8-31 *)
  ((acc intP1 x) = 1 /\ result = 0) /\
  (not_assigns alloc intP intP1 (pset_singleton x)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (HW_2: intP0 = (upd intP x 0)),
  forall (result: Z),
  forall (HW_3: result = (acc intP0 x)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_3 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (HW_2: intP0 = (upd intP x 0)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_4 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc x)),
  (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (r: pointer),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc r)),
  forall (result: Z),
  forall (intP0: ((memory) Z)),
  forall (HW_2: (* File \"pointer.c819618234.c\", line 0, characters 8-31 *)
                ((acc intP0 r) = 1 /\ result = 0) /\
                (not_assigns alloc intP intP0 (pset_singleton r))),
  (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 32-39 *)
  (acc intP0 r) = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (result: pointer),
  forall (alloc0: alloc_table),
  forall (HW_1: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (intP0: ((memory) Z)),
  forall (HW_2: intP0 = (upd intP result 0)),
  forall (result0: Z),
  forall (intP1: ((memory) Z)),
  forall (HW_3: (* File \"pointer.c819618234.c\", line 0, characters 8-31 *)
                ((acc intP1 result) = 1 /\ result0 = 0) /\
                (not_assigns alloc0 intP0 intP1 (pset_singleton result))),
  forall (result1: Z),
  forall (HW_4: result1 = (acc intP1 result)),
  (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 9-21 *)
  (result0 + result1) = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (result: pointer),
  forall (alloc0: alloc_table),
  forall (HW_1: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 1 /\
                (valid_range alloc0 result 0 (1 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (intP0: ((memory) Z)),
  forall (HW_2: intP0 = (upd intP result 0)),
  (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
  (valid alloc0 result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_3 : 
  1 >= 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) pointer)),
  forall (y: ((memory) Z)),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc s) /\ (valid_range alloc s 0 0) /\
                (valid1_range x 1) /\ (valid1 x)),
  forall (result: pointer),
  forall (HW_2: result = (acc x s)),
  forall (intP0: ((memory) Z)),
  forall (HW_3: intP0 = (upd intP result 1)),
  forall (y0: ((memory) Z)),
  forall (HW_4: y0 = (upd y s 2)),
  forall (result0: Z),
  forall (HW_5: result0 = (acc intP0 result)),
  (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 29-41 *)
  result0 >= 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) pointer)),
  forall (y: ((memory) Z)),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc s) /\ (valid_range alloc s 0 0) /\
                (valid1_range x 1) /\ (valid1 x)),
  forall (result: pointer),
  forall (HW_2: result = (acc x s)),
  forall (intP0: ((memory) Z)),
  forall (HW_3: intP0 = (upd intP result 1)),
  forall (y0: ((memory) Z)),
  forall (HW_4: y0 = (upd y s 2)),
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) pointer)),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc s) /\ (valid_range alloc s 0 0) /\
                (valid1_range x 1) /\ (valid1 x)),
  forall (result: pointer),
  forall (HW_2: result = (acc x s)),
  forall (intP0: ((memory) Z)),
  forall (HW_3: intP0 = (upd intP result 1)),
  (valid alloc s).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (s: pointer),
  forall (x: ((memory) pointer)),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc s) /\ (valid_range alloc s 0 0) /\
                (valid1_range x 1) /\ (valid1 x)),
  forall (result: pointer),
  forall (HW_2: result = (acc x s)),
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", line 0, characters 0-0: *)
(*Why goal*) Lemma struct1_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (s: pointer),
  forall (x: ((memory) pointer)),
  forall (HW_1: (* File \"pointer.c819618234.c1069824147.i\", line 0, characters 10-19 *)
                (valid alloc s) /\ (valid_range alloc s 0 0) /\
                (valid1_range x 1) /\ (valid1 x)),
  (valid alloc s).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

