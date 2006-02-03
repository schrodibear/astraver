
Require Export assigns_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_1 : 
  forall (p: ((pointer) global)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  (not_assigns alloc intM_global intM_global
   (pset_range (pset_singleton p) 0 (size - 1))) /\
  (* File "assigns.c", line 8, characters 7-64 *) ((0 <= size /\ size <=
  size) /\ p = (shift p (size - size))).
Proof.
intuition.
replace (size-size) with 0.
rewrite shift_zero.
auto.
omega.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_2 : 
  forall (p: ((pointer) global)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc intM_global intM_global
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_global0: ((memory) Z global)),
  forall (mutable_p: ((pointer) global)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc intM_global intM_global0
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  (valid alloc mutable_p).
Proof.
intuition.
subst mutable_p.
apply valid_range_valid_shift with 0 (size-1);auto.
omega.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_3 : 
  forall (p: ((pointer) global)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc intM_global intM_global
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_global0: ((memory) Z global)),
  forall (mutable_p: ((pointer) global)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc intM_global intM_global0
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_6: (valid alloc mutable_p)),
  forall (intM_global1: ((memory) Z global)),
  forall (HW_7: intM_global1 = (upd intM_global0 mutable_p 0)),
  forall (result: ((pointer) global)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) global)),
  forall (HW_9: mutable_p0 = result),
  ((not_assigns alloc intM_global intM_global1
    (pset_range (pset_singleton p) 0 (size - 1))) /\
  (* File "assigns.c", line 8, characters 7-64 *) ((0 <= mutable_size0 /\
  mutable_size0 <= size) /\ mutable_p0 = (shift p (size - mutable_size0)))) /\
  (Zwf 0 mutable_size0 mutable_size).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

