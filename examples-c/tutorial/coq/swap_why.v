(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/swap.why", characters 154-181 *)
Lemma swap_impl_po_1 : 
  forall (t: pointer),
  forall (i: Z),
  forall (j: Z),
  forall (alloc: alloc_table),
  forall (Pre10: (valid_index alloc t i) /\ (valid_index alloc t j)),
  (valid alloc (shift t i)).
Proof.
intuition.
subst; auto.
Save.

(* Why obligation from file "why/swap.why", characters 263-290 *)
Lemma swap_impl_po_2 : 
  forall (t: pointer),
  forall (i: Z),
  forall (j: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_index alloc t i) /\ (valid_index alloc t j)),
  forall (Pre9: (valid alloc (shift t i))),
  forall (tmp: Z),
  forall (Post8: tmp = (acc intP (shift t i))),
  forall (caduceus_2: pointer),
  forall (Post4: caduceus_2 = (shift t i)),
  (valid alloc (shift t j)).
Proof.
intuition; subst; auto.
assert (i=j \/ i<>j); [omega | intuition].
subst i; caduceus.
caduceus.
caduceus.
Save.

(* Why obligation from file "why/swap.why", characters 237-291 *)
Lemma swap_impl_po_3 : 
  forall (t: pointer),
  forall (i: Z),
  forall (j: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_index alloc t i) /\ (valid_index alloc t j)),
  forall (Pre9: (valid alloc (shift t i))),
  forall (tmp: Z),
  forall (Post8: tmp = (acc intP (shift t i))),
  forall (caduceus_2: pointer),
  forall (Post4: caduceus_2 = (shift t i)),
  forall (Pre4: (valid alloc (shift t j))),
  forall (aux_3: Z),
  forall (Post3: aux_3 = (acc intP (shift t j))),
  (valid alloc caduceus_2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/swap.why", characters 237-291 *)
Lemma swap_impl_po_4 : 
  forall (t: pointer),
  forall (i: Z),
  forall (j: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_index alloc t i) /\ (valid_index alloc t j)),
  forall (Pre9: (valid alloc (shift t i))),
  forall (tmp: Z),
  forall (Post8: tmp = (acc intP (shift t i))),
  forall (caduceus_2: pointer),
  forall (Post4: caduceus_2 = (shift t i)),
  forall (Pre4: (valid alloc (shift t j))),
  forall (aux_3: Z),
  forall (Post3: aux_3 = (acc intP (shift t j))),
  forall (Pre1: (valid alloc caduceus_2)),
  forall (intP0: ((memory) Z)),
  forall (Post11: intP0 = (upd intP caduceus_2 aux_3)),
  (forall (result:pointer),
   (result = (shift t j) ->
    (forall (intP1:((memory) Z)),
     (intP1 = (upd intP0 result tmp) -> (acc intP1 (shift t i)) =
      (acc intP (shift t j)) /\ (acc intP1 (shift t j)) =
      (acc intP (shift t i)))) /\
    (valid alloc result))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

