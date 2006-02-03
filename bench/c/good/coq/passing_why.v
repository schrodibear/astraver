(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export passing_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (x: ((pointer) global)),
  forall (alloc: alloc_table),
  forall (t: ((pointer) global)),
  forall (HW_1: (* File "passing.c", line 21, characters 14-31 *)
                (valid_index alloc x 0) /\ (valid_range alloc t 0 1)),
  (valid alloc x).
Proof.
intuition.
subst; auto.
rewrite <- shift_zero;apply valid_index_valid_shift;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (x: ((pointer) global)),
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (t: ((pointer) global)),
  forall (HW_1: (* File "passing.c", line 21, characters 14-31 *)
                (valid_index alloc x 0) /\ (valid_range alloc t 0 1)),
  forall (HW_2: (valid alloc x)),
  forall (intM_global0: ((memory) Z global)),
  forall (HW_3: intM_global0 = (upd intM_global x 1)),
  (* File "passing.c", line 21, characters 53-62 *) (acc intM_global0 x) = 1 /\
  (not_assigns alloc intM_global intM_global0 (pset_singleton x)).
Proof.
intuition.
subst; caduceus.
red;intros.
subst.
rewrite acc_upd_neq;auto.
assert (p<> x).
apply pset_singleton_elim;auto.
auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g2_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (r: ((pointer) global)),
  forall (t: ((pointer) global)),
  forall (HW_1: (* File "passing.c", line 13, characters 14-23 *)
                (valid alloc r) /\ (valid_range alloc t 0 1)),
  forall (HW_2: (* File "passing.c", line 8, characters 14-23 *)
                (valid alloc r)),
  forall (intM_global0: ((memory) Z global)),
  forall (HW_3: (* File "passing.c", line 8, characters 43-50 *)
                (acc intM_global0 r) = 0 /\
                (not_assigns alloc intM_global intM_global0
                 (pset_singleton r))),
  forall (HW_4: (valid alloc r)),
  forall (result: Z),
  forall (HW_5: result = (acc intM_global0 r)),
  (* File "passing.c", line 13, characters 32-44 *) result = 0.
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

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (x: ((pointer) global)),
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (t: ((pointer) global)),
  forall (HW_1: (* File "passing.c", line 8, characters 14-23 *)
                (valid alloc x) /\ (valid_range alloc t 0 1)),
  forall (HW_2: (valid alloc x)),
  forall (intM_global0: ((memory) Z global)),
  forall (HW_3: intM_global0 = (upd intM_global x 0)),
  (* File "passing.c", line 8, characters 43-50 *) (acc intM_global0 x) = 0 /\
  (not_assigns alloc intM_global intM_global0 (pset_singleton x)).
Proof.
intuition.
Save.


Proof.
intuition.
subst; caduceus.
red;intros.
subst.
rewrite acc_upd_neq;auto.
assert (p<>x).
apply pset_singleton_elim;auto.
auto.
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma main_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (t: ((pointer) global)),
  forall (HW_1: (valid_range alloc t 0 1)),
  (* File "passing.c", line 21, characters 14-31 *) (valid_index alloc t 0).
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

