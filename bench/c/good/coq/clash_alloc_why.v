(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export clash_alloc_spec_why.

(* Why obligation from file "why/clash_alloc.why", characters 134-151 *)
Lemma f_impl_po_1 : 
  forall (p: pointer),
  forall (alloc: alloc_table),
  forall (Pre2: (* File \"clash_alloc.c\", line 6, characters 14-23 *)
                (valid alloc p)),
  (valid alloc p).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

