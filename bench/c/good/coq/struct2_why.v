(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export struct2_spec_why.

(* Why obligation from file "why/struct2.why", characters 153-230 *)
Lemma f_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (s0: pointer),
  forall (Pre5: (valid1 b) /\ (valid_range alloc s0 0 0) /\
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
  forall (Pre5: (valid1 b) /\ (valid_range alloc s0 0 0) /\
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


(* Why obligation from file "why/struct2.why", characters 136-265 *)
Lemma f_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (intP: ((memory) Z)),
  forall (s0: pointer),
  forall (Pre5: (valid1 b) /\ (valid_range alloc s0 0 0) /\
                (valid1_range b 5)),
  forall (Pre4: (valid alloc s0)),
  forall (caduceus_2: pointer),
  forall (Post3: caduceus_2 = (shift (acc b s0) 2)),
  forall (Pre3: (valid alloc caduceus_2)),
  forall (intP0: ((memory) Z)),
  forall (Post5: intP0 = (upd intP caduceus_2 1)),
  (* File \"struct2.c\", line 6, characters 13-18 *) True.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/struct2.why", characters 540-627 *)
Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (d: ((memory) pointer)),
  forall (u: pointer),
  forall (Pre7: (valid_range alloc u 0 0) /\ (valid1 b) /\ (valid1 d) /\
                (separation2 d d) /\ (valid1_range b 5)),
  (valid alloc u).
Proof.
intuition.
Save.

(* Why obligation from file "why/struct2.why", characters 540-627 *)
Lemma g_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (d: ((memory) pointer)),
  forall (u: pointer),
  forall (Pre7: (valid_range alloc u 0 0) /\ (valid1 b) /\ (valid1 d) /\
                (separation2 d d) /\ (valid1_range b 5)),
  forall (Pre4: (valid alloc u)),
  (valid alloc (acc d u)).
Proof.
intuition.
Save.

(* Why obligation from file "why/struct2.why", characters 635-662 *)
Lemma g_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (d: ((memory) pointer)),
  forall (u: pointer),
  forall (Pre7: (valid_range alloc u 0 0) /\ (valid1 b) /\ (valid1 d) /\
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

(* Why obligation from file "why/struct2.why", characters 523-662 *)
Lemma g_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (d: ((memory) pointer)),
  forall (intP: ((memory) Z)),
  forall (u: pointer),
  forall (Pre7: (valid_range alloc u 0 0) /\ (valid1 b) /\ (valid1 d) /\
                (separation2 d d) /\ (valid1_range b 5)),
  forall (Pre4: (valid alloc u)),
  forall (Pre6: (valid alloc (acc d u))),
  forall (caduceus_2: pointer),
  forall (Post3: caduceus_2 = (shift (acc b (acc d u)) 2)),
  forall (Pre3: (valid alloc caduceus_2)),
  forall (intP0: ((memory) Z)),
  forall (Post5: intP0 = (upd intP caduceus_2 1)),
  (* File \"struct2.c\", line 16, characters 13-18 *) True.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

