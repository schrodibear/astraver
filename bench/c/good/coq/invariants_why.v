(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/invariants.why", characters 384-442 *)
Lemma f_impl_po_1 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (valid alloc s) /\
                (~((base_addr c) = (base_addr s)) /\
                (valid_range alloc c 0 1)) /\ (0 <= (acc x s) /\ (acc x s) <=
                (acc y s)) /\ (acc y s) <= 100),
  (valid alloc s).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/invariants.why", characters 583-709 *)
Lemma f_impl_po_2 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (valid alloc s) /\
                (~((base_addr c) = (base_addr s)) /\
                (valid_range alloc c 0 1)) /\ (0 <= (acc x s) /\ (acc x s) <=
                (acc y s)) /\ (acc y s) <= 100),
  forall (Pre6: (valid alloc s)),
  forall (t: Z),
  forall (Post7: t = ((acc x s) + n)),
  forall (Pre5: (valid alloc s)),
  forall (Test2: t <= ((acc y s) - 20)),
  forall (caduceus_2: pointer),
  forall (Post5: caduceus_2 = s),
  (valid alloc (shift c 0)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/invariants.why", characters 560-710 *)
Lemma f_impl_po_3 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (valid alloc s) /\
                (~((base_addr c) = (base_addr s)) /\
                (valid_range alloc c 0 1)) /\ (0 <= (acc x s) /\ (acc x s) <=
                (acc y s)) /\ (acc y s) <= 100),
  forall (Pre6: (valid alloc s)),
  forall (t: Z),
  forall (Post7: t = ((acc x s) + n)),
  forall (Pre5: (valid alloc s)),
  forall (Test2: t <= ((acc y s) - 20)),
  forall (caduceus_2: pointer),
  forall (Post5: caduceus_2 = s),
  forall (Pre4: (valid alloc (shift c 0))),
  forall (aux_4: Z),
  forall (Post4: aux_4 = (t + (acc intP (shift c 0)))),
  (valid alloc caduceus_2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/invariants.why", characters 560-710 *)
Lemma f_impl_po_4 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (valid alloc s) /\
                (~((base_addr c) = (base_addr s)) /\
                (valid_range alloc c 0 1)) /\ (0 <= (acc x s) /\ (acc x s) <=
                (acc y s)) /\ (acc y s) <= 100),
  forall (Pre6: (valid alloc s)),
  forall (t: Z),
  forall (Post7: t = ((acc x s) + n)),
  forall (Pre5: (valid alloc s)),
  forall (Test2: t <= ((acc y s) - 20)),
  forall (caduceus_2: pointer),
  forall (Post5: caduceus_2 = s),
  forall (Pre4: (valid alloc (shift c 0))),
  forall (aux_4: Z),
  forall (Post4: aux_4 = (t + (acc intP (shift c 0)))),
  forall (Pre1: (valid alloc caduceus_2)),
  forall (x0: ((memory) Z)),
  forall (Post13: x0 = (upd x caduceus_2 aux_4)),
  (0 <= (acc x0 s) /\ (acc x0 s) <= (acc y s)) /\ (acc y s) <= 100.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/invariants.why", characters 718-722 *)
Lemma f_impl_po_5 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (valid alloc s) /\
                (~((base_addr c) = (base_addr s)) /\
                (valid_range alloc c 0 1)) /\ (0 <= (acc x s) /\ (acc x s) <=
                (acc y s)) /\ (acc y s) <= 100),
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
(* FILL PROOF HERE *)
Save.

