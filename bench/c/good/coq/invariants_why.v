(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/invariants.why", characters 349-406 *)
Lemma f_impl_po_1 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: (n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (0 <= (acc x s) /\
                (acc x s) <= (acc y s)) /\ (acc y s) <= 100) /\
                (valid alloc s) /\ ~((base_addr c) = (base_addr s)) /\
                (valid_range alloc c 0 1)),
  (valid alloc s).
Proof.
intuition.
Save.

(* Why obligation from file "why/invariants.why", characters 552-594 *)
Lemma f_impl_po_2 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: (n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (0 <= (acc x s) /\
                (acc x s) <= (acc y s)) /\ (acc y s) <= 100) /\
                (valid alloc s) /\ ~((base_addr c) = (base_addr s)) /\
                (valid_range alloc c 0 1)),
  forall (Pre6: (valid alloc s)),
  forall (t: Z),
  forall (Post7: t = ((acc x s) + n)),
  forall (Pre5: (valid alloc s)),
  forall (Test2: t <= ((acc y s) - 20)),
  forall (caduceus_1: pointer),
  forall (Post5: caduceus_1 = s),
  (valid alloc (shift c 0)).
Proof.
intuition.
Save.

(* Why obligation from file "why/invariants.why", characters 529-595 *)
Lemma f_impl_po_3 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: (n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (0 <= (acc x s) /\
                (acc x s) <= (acc y s)) /\ (acc y s) <= 100) /\
                (valid alloc s) /\ ~((base_addr c) = (base_addr s)) /\
                (valid_range alloc c 0 1)),
  forall (Pre6: (valid alloc s)),
  forall (t: Z),
  forall (Post7: t = ((acc x s) + n)),
  forall (Pre5: (valid alloc s)),
  forall (Test2: t <= ((acc y s) - 20)),
  forall (caduceus_1: pointer),
  forall (Post5: caduceus_1 = s),
  forall (Pre4: (valid alloc (shift c 0))),
  forall (aux_4: Z),
  forall (Post4: aux_4 = (t + (acc intP (shift c 0)))),
  (valid alloc caduceus_1).
Proof.
intuition.
subst; auto.
Save.

(* Why obligation from file "why/invariants.why", characters 529-595 *)
Lemma f_impl_po_4 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: (n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (0 <= (acc x s) /\
                (acc x s) <= (acc y s)) /\ (acc y s) <= 100) /\
                (valid alloc s) /\ ~((base_addr c) = (base_addr s)) /\
                (valid_range alloc c 0 1)),
  forall (Pre6: (valid alloc s)),
  forall (t: Z),
  forall (Post7: t = ((acc x s) + n)),
  forall (Pre5: (valid alloc s)),
  forall (Test2: t <= ((acc y s) - 20)),
  forall (caduceus_1: pointer),
  forall (Post5: caduceus_1 = s),
  forall (Pre4: (valid alloc (shift c 0))),
  forall (aux_4: Z),
  forall (Post4: aux_4 = (t + (acc intP (shift c 0)))),
  forall (Pre1: (valid alloc caduceus_1)),
  forall (x0: ((memory) Z)),
  forall (Post13: x0 = (upd x caduceus_1 aux_4)),
  (0 <= (acc x0 s) /\ (acc x0 s) <= (acc y s)) /\ (acc y s) <= 100.
Proof.
intuition.
subst; caduceus.
subst; caduceus.
Save.

(* Why obligation from file "why/invariants.why", characters 605-605 *)
Lemma f_impl_po_5 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: (n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (0 <= (acc x s) /\
                (acc x s) <= (acc y s)) /\ (acc y s) <= 100) /\
                (valid alloc s) /\ ~((base_addr c) = (base_addr s)) /\
                (valid_range alloc c 0 1)),
  forall (Pre6: (valid alloc s)),
  forall (t: Z),
  forall (Post7: t = ((acc x s) + n)),
  forall (Pre5: (valid alloc s)),
  forall (Test1: t > ((acc y s) - 20)),
  forall (result0: unit),
  forall (Post1: result0 = tt),
  (0 <= (acc x s) /\ (acc x s) <= (acc y s)) /\ (acc y s) <= 100.
Proof.
intuition.
Save.

(* Why obligation from file "why/invariants.why", characters 936-964 *)
Lemma invariants_initially_established_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (s: pointer),
  forall (Pre7: (valid alloc s) /\ ~((base_addr c) = (base_addr s)) /\
                (valid_range alloc c 0 1)),
  forall (caduceus_2: pointer),
  forall (Post3: caduceus_2 = (shift c 0)),
  (valid alloc caduceus_2).
Proof.
intros;subst.
inversion_clear Pre7.
inversion_clear H0.
apply valid_range_valid_shift with 0 1;auto.
omega.
Save.

(* Why obligation from file "why/invariants.why", characters 900-964 *)
Lemma invariants_initially_established_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: (valid alloc s) /\ ~((base_addr c) = (base_addr s)) /\
                (valid_range alloc c 0 1)),
  forall (caduceus_2: pointer),
  forall (Post3: caduceus_2 = (shift c 0)),
  forall (Pre3: (valid alloc caduceus_2)),
  forall (intP0: ((memory) Z)),
  forall (Post7: intP0 = (upd intP caduceus_2 12)),
  (forall (result:pointer),
   (result = (shift c 1) ->
    (forall (intP:((memory) Z)),
     (intP = (upd intP0 result 14) -> ((0 <= (acc x s) /\ (acc x s) <=
      (acc y s)) /\ (acc y s) <= 100) /\ (acc intP (shift c 0)) = 12)) /\
    (valid alloc result))).
Proof.
intuition.
Admitted.

