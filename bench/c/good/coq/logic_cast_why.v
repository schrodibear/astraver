(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/logic_cast.why", characters 298-326 *)
Lemma f_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (t: pointer),
  forall (Pre7: (valid_t t alloc)),
  forall (I1: Z),
  forall (Post1: I1 = 0),
  forall (Variant1: Z),
  forall (I2: Z),
  forall (Pre6: Variant1 = (4 - I2)),
  forall (Pre5: 0 <= I2 /\ I2 <= 4),
  forall (Test2: I2 < 4),
  forall (caduceus_1: pointer),
  forall (Post5: caduceus_1 = (shift t I2)),
  (valid alloc caduceus_1).
Proof.
intuition.
unfold valid_t in Pre7.
subst; auto.
Save.

(* Why obligation from file "why/logic_cast.why", characters 261-326 *)
Lemma f_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (t: pointer),
  forall (Pre7: (valid_t t alloc)),
  forall (I1: Z),
  forall (Post1: I1 = 0),
  forall (Variant1: Z),
  forall (I2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre6: Variant1 = (4 - I2)),
  forall (Pre5: 0 <= I2 /\ I2 <= 4),
  forall (Test2: I2 < 4),
  forall (caduceus_1: pointer),
  forall (Post5: caduceus_1 = (shift t I2)),
  forall (Pre4: (valid alloc caduceus_1)),
  forall (intP1: ((memory) Z)),
  forall (Post15: intP1 = (upd intP0 caduceus_1 I2)),
  (forall (I:Z),
   (I = (I2 + 1) -> (0 <= I /\ I <= 4) /\ (Zwf 0 (4 - I) (4 - I2)))).
Proof.
intuition.
Save.

(* Why obligation from file "why/logic_cast.why", characters 200-230 *)
Lemma f_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (t: pointer),
  forall (Pre7: (valid_t t alloc)),
  forall (I1: Z),
  forall (Post1: I1 = 0),
  0 <= I1 /\ I1 <= 4.
Proof.
intuition.
Save.

