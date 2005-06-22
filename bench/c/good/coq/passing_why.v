(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export passing_spec_why.

(* Why obligation from file "why/passing.why", characters 144-162 *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (Pre4: (* File \"passing.c\", line 21, characters 14-31 *)
                (valid_index alloc x 0)),
  (valid alloc x).
Proof.
intuition.
subst; auto.
rewrite <- shift_zero;apply valid_index_valid_shift;auto.
Save.

(* Why obligation from file "why/passing.why", characters 37-315 *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre4: (* File \"passing.c\", line 21, characters 14-31 *)
                (valid_index alloc x 0)),
  forall (Pre3: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post3: intP0 = (upd intP x 1)),
  (* File \"passing.c\", line 21, characters 53-62 *) (acc intP0 x) = 1 /\
  (not_assigns alloc intP intP0 (pset_singleton x)).
Proof.
intuition.
subst; caduceus.
Save.

(* Why obligation from file "why/passing.why", characters 448-463 *)
(*Why goal*) Lemma g2_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (r: pointer),
  forall (Pre5: (* File \"passing.c\", line 13, characters 14-23 *)
                (valid alloc r)),
  (* File \"passing.c\", line 8, characters 14-23 *) (valid alloc r).
Proof.
intuition.
Save.

(* Why obligation from file "why/passing.why", characters 466-481 *)
(*Why goal*) Lemma g2_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (r: pointer),
  forall (Pre5: (* File \"passing.c\", line 13, characters 14-23 *)
                (valid alloc r)),
  forall (Pre4: (* File \"passing.c\", line 8, characters 14-23 *)
                (valid alloc r)),
  forall (intP0: ((memory) Z)),
  forall (Post3: (* File \"passing.c\", line 8, characters 43-50 *)
                 (acc intP0 r) = 0 /\
                 (not_assigns alloc intP intP0 (pset_singleton r))),
  (valid alloc r).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/passing.why", characters 354-561 *)
(*Why goal*) Lemma g2_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (r: pointer),
  forall (Pre5: (* File \"passing.c\", line 13, characters 14-23 *)
                (valid alloc r)),
  forall (Pre4: (* File \"passing.c\", line 8, characters 14-23 *)
                (valid alloc r)),
  forall (intP0: ((memory) Z)),
  forall (Post3: (* File \"passing.c\", line 8, characters 43-50 *)
                 (acc intP0 r) = 0 /\
                 (not_assigns alloc intP intP0 (pset_singleton r))),
  forall (Pre3: (valid alloc r)),
  forall (result0: Z),
  forall (Post2: result0 = (acc intP0 r)),
  (* File \"passing.c\", line 13, characters 32-44 *) result0 = 0.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/passing.why", characters 694-712 *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (Pre4: (* File \"passing.c\", line 8, characters 14-23 *)
                (valid alloc x)),
  (valid alloc x).
Proof.
intuition.
Save.


(* Why obligation from file "why/passing.why", characters 601-864 *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre4: (* File \"passing.c\", line 8, characters 14-23 *)
                (valid alloc x)),
  forall (Pre3: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post3: intP0 = (upd intP x 0)),
  (* File \"passing.c\", line 8, characters 43-50 *) (acc intP0 x) = 0 /\
  (not_assigns alloc intP intP0 (pset_singleton x)).
Proof.
intuition.
subst; caduceus.
Save.

(* Why obligation from file "why/passing.why", characters 957-972 *)
(*Why goal*) Lemma main_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (t: pointer),
  forall (Pre4: (valid_range alloc t 0 1)),
  (* File \"passing.c\", line 21, characters 14-31 *) (valid_index alloc t 0).
Proof.
intuition.
Save.

(* Why obligation from file "why/passing.why", characters 905-1062 *)
(*Why goal*) Lemma main_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (Pre4: (valid_range alloc t 0 1)),
  forall (Pre3: (* File \"passing.c\", line 21, characters 14-31 *)
                (valid_index alloc t 0)),
  forall (intP0: ((memory) Z)),
  forall (Post2: (* File \"passing.c\", line 21, characters 53-62 *)
                 (acc intP0 t) = 1 /\
                 (not_assigns alloc intP intP0 (pset_singleton t))),
  (* File \"passing.c\", line 28, characters 13-22 *) (acc intP0 t) = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

