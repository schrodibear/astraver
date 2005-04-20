(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/struct2.why", characters 559-636 *)
Lemma f_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (s0: pointer),
  forall (Pre5: (separation2 b b) /\ (valid1 b) /\
                (valid_range alloc s0 0 1) /\ (valid_range alloc s0 0 1) /\
                (forall (index_0:pointer),
                 (forall (index_1:pointer),
                  ~((base_addr (acc b index_0)) = (base_addr (acc b index_1))))) /\
                (separation_s0_s0 alloc b s0) /\ (valid1_range b 5)),
  (valid alloc s0).
Proof.
intuition.
Save.

(* Why obligation from file "why/struct2.why", characters 644-671 *)
Lemma f_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (s0: pointer),
  forall (Pre5: (separation2 b b) /\ (valid1 b) /\
                (valid_range alloc s0 0 1) /\ (valid_range alloc s0 0 1) /\
                (forall (index_0:pointer),
                 (forall (index_1:pointer),
                  ~((base_addr (acc b index_0)) = (base_addr (acc b index_1))))) /\
                (separation_s0_s0 alloc b s0) /\ (valid1_range b 5)),
  forall (Pre4: (valid alloc s0)),
  forall (caduceus_2: pointer),
  forall (Post3: caduceus_2 = (shift (acc b s0) 2)),
  (valid alloc caduceus_2).
Proof.
intuition.
subst.
unfold valid1_range in H6.
generalize (H6 s0 alloc Pre4).
intuition.
Save.

(* Why obligation from file "why/struct2.why", characters 1325-1412 *)
Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (d: ((memory) pointer)),
  forall (u: pointer),
  forall (Pre7: (separation2 b b) /\ (valid_range alloc u 0 1) /\
                (valid_range alloc u 0 1) /\ (valid1 b) /\ (valid1 d) /\
                (forall (index_0:pointer),
                 (forall (index_1:pointer),
                  ~((base_addr (acc b index_0)) = (base_addr (acc b index_1))))) /\
                (separation_u_u alloc d u) /\ (separation2 d d) /\
                (valid1_range b 5)),
  (valid alloc u).
Proof.
intuition.
Save.

(* Why obligation from file "why/struct2.why", characters 1325-1412 *)
Lemma g_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (d: ((memory) pointer)),
  forall (u: pointer),
  forall (Pre7: (separation2 b b) /\ (valid_range alloc u 0 1) /\
                (valid_range alloc u 0 1) /\ (valid1 b) /\ (valid1 d) /\
                (forall (index_0:pointer),
                 (forall (index_1:pointer),
                  ~((base_addr (acc b index_0)) = (base_addr (acc b index_1))))) /\
                (separation_u_u alloc d u) /\ (separation2 d d) /\
                (valid1_range b 5)),
  forall (Pre4: (valid alloc u)),
  (valid alloc (acc d u)).
Proof.
intuition.
Save.

(* Why obligation from file "why/struct2.why", characters 1420-1447 *)
Lemma g_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (d: ((memory) pointer)),
  forall (u: pointer),
  forall (Pre7: (separation2 b b) /\ (valid_range alloc u 0 1) /\
                (valid_range alloc u 0 1) /\ (valid1 b) /\ (valid1 d) /\
                (forall (index_0:pointer),
                 (forall (index_1:pointer),
                  ~((base_addr (acc b index_0)) = (base_addr (acc b index_1))))) /\
                (separation_u_u alloc d u) /\ (separation2 d d) /\
                (valid1_range b 5)),
  forall (Pre4: (valid alloc u)),
  forall (Pre6: (valid alloc (acc d u))),
  forall (caduceus_2: pointer),
  forall (Post3: caduceus_2 = (shift (acc b (acc d u)) 2)),
  (valid alloc caduceus_2).
Proof.
intuition.
subst.
unfold valid1_range in H8.
generalize (H8 (u#d) alloc Pre6);intuition.
Save.

