(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export assigns_spec_why.


(* Why obligation from file "why/assigns.why", characters 309-418 *)
Lemma erase_impl_po_1 : 
  forall (p: pointer),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre7: size >= 0 /\ (valid_range alloc p 0 (size - 1))),
  forall (mutable_p: pointer),
  forall (Post10: mutable_p = p),
  forall (mutable_size: Z),
  forall (Post9: mutable_size = size),
  forall (Variant1: Z),
  forall (intP0: ((memory) Z)),
  forall (mutable_p1: pointer),
  forall (mutable_size1: Z),
  forall (Pre6: Variant1 = mutable_size1),
  forall (Pre5: (not_assigns alloc intP intP0
                 (pset_range (pset_singleton mutable_p) 0 (mutable_size - 1))) /\
                (0 <= mutable_size1 /\ mutable_size1 <= mutable_size) /\
                mutable_p1 = (shift (shift mutable_p mutable_size)
                              (Zopp mutable_size1))),
  forall (Test2: true = true),
  forall (caduceus: Z),
  forall (Post4: caduceus = mutable_size1),
  forall (mutable_size2: Z),
  forall (Post2: mutable_size2 = (caduceus - 1)),
  forall (result1: Z),
  forall (Post3: result1 = caduceus),
  ((result1 <> 0 ->
    (forall (result:pointer),
     (result = mutable_p1 ->
      (forall (intP1:((memory) Z)),
       (intP1 = (upd intP0 result 0) ->
        (forall (mutable_p0:pointer),
         (mutable_p0 = (shift mutable_p1 1) ->
          ((not_assigns alloc intP intP1
            (pset_range (pset_singleton mutable_p) 0 (mutable_size - 1))) /\
          (0 <= mutable_size2 /\ mutable_size2 <= mutable_size) /\
          mutable_p0 = (shift (shift mutable_p mutable_size)
                        (Zopp mutable_size2))) /\
          (Zwf 0 mutable_size2 mutable_size1))))) /\
      (valid alloc result))))) /\
  ((result1 = 0 ->
    (not_assigns alloc intP intP0
     (pset_range (pset_singleton p) 0 (size - 1))))).
Proof.
intuition; subst; auto.
apply not_assigns_trans with intP0; auto.
rewrite shift_shift; red; intuition.
rewrite acc_upd_neq; auto.
assert (shift p (size + - mutable_size1)<> p0).
apply pset_range_elim with (pset_singleton p) 0 (size-1); auto with *.
auto with *.

autorewrite with caduceus.
replace  (- (mutable_size1 - 1)) with (-mutable_size1+1); auto with *.
Save.

(* Why obligation from file "why/assigns.why", characters 484-854 *)
Lemma erase_impl_po_2 : 
  forall (p: pointer),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre7: size >= 0 /\ (valid_range alloc p 0 (size - 1))),
  forall (mutable_p: pointer),
  forall (Post10: mutable_p = p),
  forall (mutable_size: Z),
  forall (Post9: mutable_size = size),
  (not_assigns alloc intP intP
   (pset_range (pset_singleton mutable_p) 0 (mutable_size - 1))) /\
  (0 <= mutable_size /\ mutable_size <= mutable_size) /\
  mutable_p = (shift (shift mutable_p mutable_size) (Zopp mutable_size)).
Proof.
intuition.
subst; autorewrite with caduceus.
replace (size + - size) with 0; auto with *.
autorewrite with caduceus; auto.
Save.

