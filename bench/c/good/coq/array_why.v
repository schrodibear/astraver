(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/array.why", characters 340-432 *)
Lemma getcell_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (intPP: ((memory) pointer)),
  forall (t: pointer),
  forall (Pre5: ((valid_index alloc t 1) /\
                (valid_index alloc (acc intPP (shift t 1)) 2)) /\
                (forall (index_1:Z),
                 (0 <= index_1 /\ index_1 < 3 ->
                  (valid_range alloc (shift t index_1) 0 2)))),
  forall (caduceus_1: pointer),
  forall (Post1: caduceus_1 = t),
  forall (result: pointer),
  forall (Post3: result = (shift caduceus_1 1)),
  (forall (result0:pointer),
   (result0 = (acc intPP result) ->
    (forall (result:pointer),
     (result = (shift result0 2) ->
      (forall (result0:Z), (result0 = (acc intP result) -> True)) /\
      (valid alloc result))))) /\
  (valid alloc result).
Proof.
intuition; subst; auto with *.
Save.

