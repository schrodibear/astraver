(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/passing.why", characters 86-104 *)
Lemma f_impl_po_1 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (Pre4: (valid_index alloc x 0)),
  (valid alloc x).
Proof.
intuition.
subst; auto.
rewrite <- shift_zero;apply valid_index_valid_shift;auto.
Save.

(* Why obligation from file "why/passing.why", characters 37-200 *)
Lemma f_impl_po_2 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre4: (valid_index alloc x 0)),
  forall (Pre3: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post3: intP0 = (upd intP x 1)),
  (acc intP0 x) = 1 /\ (not_assigns alloc intP intP0 (pset_singleton x)).
Proof.
intuition.
subst; caduceus.
Save.

(* Why obligation from file "why/passing.why", characters 239-342 *)
Lemma g2_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (r: pointer),
  forall (Pre4: (valid alloc r)),
  forall (intP0: ((memory) Z)),
  forall (Post3: (acc intP0 r) = 0 /\
                 (not_assigns alloc intP intP0 (pset_singleton r))),
  forall (Pre3: (valid alloc r)),
  forall (result0: Z),
  forall (Post2: result0 = (acc intP0 r)),
  result0 = 0.
Proof.
intuition.
Save.

(* Why obligation from file "why/passing.why", characters 382-536 *)
Lemma g_impl_po_1 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre3: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post3: intP0 = (upd intP x 0)),
  (acc intP0 x) = 0 /\ (not_assigns alloc intP intP0 (pset_singleton x)).
Proof.
intuition.
subst; caduceus.
Save.


(* Why obligation from file "why/passing.why", characters 693-708 *)
Lemma main_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (t: pointer),
  forall (Pre4: (valid_range alloc t 0 2) /\ (valid_range alloc t 0 2) /\
                (separation_t_t t)),
  (valid_index alloc t 0).
Proof.
intuition.
Save.

