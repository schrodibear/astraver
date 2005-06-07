(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export coord_spec_why.

(* Why obligation from file "why/coord.why", characters 148-193 *)
Lemma g_impl_po_1 : 
  forall (index: Z),
  forall (alloc: alloc_table),
  forall (tab: pointer),
  forall (Pre5: (0 <= index /\ index < 3) /\ (valid_range alloc tab 0 2)),
  (valid alloc (shift tab index)).
Proof.
intros.
intuition.
Save.
