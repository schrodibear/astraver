(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/swap.why", characters 154-182 *)
Lemma swap_impl_po_1 : 
  forall (t: pointer),
  forall (i: Z),
  forall (j: Z),
  forall (alloc: alloc),
  forall (Pre10: (valid_index alloc t i) /\ (valid_index alloc t j)),
  forall (aux_1: pointer),
  forall (Post2: aux_1 = (shift t i)),
  (valid alloc aux_1).
Proof.
intuition.
subst; auto.
Save.

(* Why obligation from file "why/swap.why", characters 154-182 *)
Lemma swap_impl_po_2 : 
  forall (t: pointer),
  forall (i: Z),
  forall (j: Z),
  forall (alloc: alloc),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_index alloc t i) /\ (valid_index alloc t j)),
  forall (aux_1: pointer),
  forall (Post2: aux_1 = (shift t i)),
  forall (Pre1: (valid alloc aux_1)),
  forall (result: Z),
  forall (Post4: result = (acc intP aux_1)),
  (forall (result0:pointer),
   (result0 = (shift t j) ->
    (forall (result1:pointer),
     (result1 = (shift t i) ->
      (forall (result2:Z),
       (result2 = (acc intP result1) ->
        (forall (intP0:((memory) Z)),
         (intP0 = (upd intP result0 result2) ->
          (forall (result0:pointer),
           (result0 = (shift t i) ->
            (forall (intP:((memory) Z)),
             (intP = (upd intP0 result0 result) -> True)) /\
            (valid alloc result0))))) /\
        (valid alloc result0))) /\
      (valid alloc result1))))).
Proof.
intuition; subst; auto.
Save.

