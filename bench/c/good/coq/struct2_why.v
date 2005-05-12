(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/struct2.why", characters 153-230 *)
Lemma f_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (s0: pointer),
  forall (Pre5: (valid1 b) /\ (valid_range alloc s0 0 1) /\
                (valid1_range b 5)),
  (valid alloc s0).
Proof.
intuition.
Save.

(* Why obligation from file "why/struct2.why", characters 238-265 *)
Lemma f_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (s0: pointer),
  forall (Pre5: (valid1 b) /\ (valid_range alloc s0 0 1) /\
                (valid1_range b 5)),
  forall (Pre4: (valid alloc s0)),
  forall (caduceus_2: pointer),
  forall (Post3: caduceus_2 = (shift (acc b s0) 2)),
  (valid alloc caduceus_2).
Proof.
intuition.
subst.
unfold valid1_range in H2.
generalize (H2 s0 alloc Pre4).
intuition.
Save.


(* Why obligation from file "why/struct2.why", characters 489-576 *)
Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (d: ((memory) pointer)),
  forall (u: pointer),
  forall (Pre7: (valid_range alloc u 0 1) /\ (valid1 b) /\ (valid1 d) /\
                (separation2 d d) /\ (valid1_range b 5)),
  (valid alloc u).
Proof.
intuition.
Save.

(* Why obligation from file "why/struct2.why", characters 489-576 *)
Lemma g_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (d: ((memory) pointer)),
  forall (u: pointer),
  forall (Pre7: (valid_range alloc u 0 1) /\ (valid1 b) /\ (valid1 d) /\
                (separation2 d d) /\ (valid1_range b 5)),
  forall (Pre4: (valid alloc u)),
  (valid alloc (acc d u)).
Proof.
intuition.
Save.

(* Why obligation from file "why/struct2.why", characters 584-611 *)
Lemma g_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (d: ((memory) pointer)),
  forall (u: pointer),
  forall (Pre7: (valid_range alloc u 0 1) /\ (valid1 b) /\ (valid1 d) /\
                (separation2 d d) /\ (valid1_range b 5)),
  forall (Pre4: (valid alloc u)),
  forall (Pre6: (valid alloc (acc d u))),
  forall (caduceus_2: pointer),
  forall (Post3: caduceus_2 = (shift (acc b (acc d u)) 2)),
  (valid alloc caduceus_2).
Proof.
intuition.
subst.
unfold valid1_range in H4.
generalize (H4 (u#d) alloc Pre6);intuition.
Save.

