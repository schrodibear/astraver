(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export passing_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (A777:Set),
  forall (x: ((pointer) A777)),
  forall (alloc: alloc_table),
  forall (t: ((pointer) Z11)),
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
  forall (A778:Set),
  forall (x: ((pointer) A778)),
  forall (alloc: alloc_table),
  forall (int_Z10: ((memory) Z A778)),
  forall (t: ((pointer) Z11)),
  forall (HW_1: (* File "passing.c", line 21, characters 14-31 *)
                (valid_index alloc x 0) /\ (valid_range alloc t 0 1)),
  forall (HW_2: (valid alloc x)),
  forall (int_Z10_0: ((memory) Z A778)),
  forall (HW_3: int_Z10_0 = (upd int_Z10 x 1)),
  (* File "passing.c", line 21, characters 53-62 *) (acc int_Z10_0 x) = 1 /\
  (not_assigns alloc int_Z10 int_Z10_0 (pset_singleton x)).
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
  forall (int_Z9: ((memory) Z Z9)),
  forall (r: ((pointer) Z9)),
  forall (t: ((pointer) Z11)),
  forall (HW_1: (* File "passing.c", line 13, characters 14-23 *)
                (valid alloc r) /\ (valid_range alloc t 0 1)),
  forall (HW_2: (* File "passing.c", line 8, characters 14-23 *)
                (valid alloc r)),
  forall (int_Z9_0: ((memory) Z Z9)),
  forall (HW_3: (* File "passing.c", line 8, characters 43-50 *)
                (acc int_Z9_0 r) = 0 /\
                (not_assigns alloc int_Z9 int_Z9_0 (pset_singleton r))),
  forall (HW_4: (valid alloc r)),
  forall (result: Z),
  forall (HW_5: result = (acc int_Z9_0 r)),
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

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (A779:Set),
  forall (x: ((pointer) A779)),
  forall (alloc: alloc_table),
  forall (int_Z8: ((memory) Z A779)),
  forall (t: ((pointer) Z11)),
  forall (HW_1: (* File "passing.c", line 8, characters 14-23 *)
                (valid alloc x) /\ (valid_range alloc t 0 1)),
  forall (HW_2: (valid alloc x)),
  forall (int_Z8_0: ((memory) Z A779)),
  forall (HW_3: int_Z8_0 = (upd int_Z8 x 0)),
  (* File "passing.c", line 8, characters 43-50 *) (acc int_Z8_0 x) = 0 /\
  (not_assigns alloc int_Z8 int_Z8_0 (pset_singleton x)).
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

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma main_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (t: ((pointer) Z11)),
  forall (HW_1: (valid_range alloc t 0 1)),
  (* File "passing.c", line 21, characters 14-31 *) (valid_index alloc t 0).
Proof.
intuition.
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

