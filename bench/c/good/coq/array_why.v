(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/array.why", characters 219-322 *)
Lemma getcell_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intPP: ((memory) pointer)),
  forall (t: pointer),
  forall (Pre5: ((valid_index alloc t 1) /\
                (valid_index alloc (acc intPP (shift t 1)) 2)) /\
                (separation_intern_t t) /\ (valid_t intPP t alloc)),
  (valid alloc (shift t 1)).
Proof.
intuition; subst; auto with *.
Save.

(* Why obligation from file "why/array.why", characters 219-322 *)
Lemma getcell_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intPP: ((memory) pointer)),
  forall (t: pointer),
  forall (Pre5: ((valid_index alloc t 1) /\
                (valid_index alloc (acc intPP (shift t 1)) 2)) /\
                (separation_intern_t t) /\ (valid_t intPP t alloc)),
  forall (Pre2: (valid alloc (shift t 1))),
  (valid alloc (shift (acc intPP (shift t 1)) 2)).
Proof.
intuition.
Save.

