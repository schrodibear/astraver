(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/ref.why", characters 75-94 *)
Lemma f_impl_po_1 : 
  1 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "why/ref.why", characters 110-151 *)
Lemma f_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre7: 1 >= 1),
  forall (alloc0: alloc_table),
  forall (i: pointer),
  forall (Post5: (valid alloc0 i) /\ (offset i) = 0 /\
                 (block_length alloc0 i) = 1 /\
                 (valid_range alloc0 i 0 (1 - 1)) /\ (fresh alloc i) /\
                 (on_stack alloc0 i) /\ (alloc_stack i alloc alloc0)),
  forall (Pre6: (valid alloc0 i)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 i) = 1 /\
                 (assigns alloc0 intP intP0 (pointer_loc i))),
  forall (Pre5: (valid alloc0 i)),
  forall (result0: Z),
  forall (Post2: result0 = (acc intP0 i)),
  result0 = 1 /\ (assigns alloc intP intP0 nothing_loc).
Proof.
intuition.
subst; auto.
red.
intros.
red in H7.
apply H7.
apply alloc_stack_valid with i alloc;auto.
apply unchanged_pointer_intro.
intro;subst.
generalize (fresh_not_valid _ _ H3 0);rewrite shift_zero.
tauto.
Save.

(* Why obligation from file "why/ref.why", characters 275-422 *)
Lemma g_impl_po_1 : 
  forall (p: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre3: (valid alloc p)),
  forall (intP0: ((memory) Z)),
  forall (Post3: intP0 = (upd intP p 1)),
  (acc intP0 p) = 1 /\ (assigns alloc intP intP0 (pointer_loc p)).
Proof.
intuition; subst; caduceus.
Save.

