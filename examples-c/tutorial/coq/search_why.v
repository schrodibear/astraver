(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/search.why", characters 430-459 *)
Lemma index_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (Post2: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre5: Variant1 = (n - i1)),
  forall (Pre4: 0 <= i1 /\
                (forall (k:Z),
                 (0 <= k /\ k < i1 -> (acc intP (shift t k)) <> v))),
  forall (Test2: i1 < n),
  forall (aux_1: pointer),
  forall (Post15: aux_1 = (shift t i1)),
  (valid alloc aux_1).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "why/search.why", characters 430-459 *)
Lemma index_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (Post2: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre5: Variant1 = (n - i1)),
  forall (Pre4: 0 <= i1 /\
                (forall (k:Z),
                 (0 <= k /\ k < i1 -> (acc intP (shift t k)) <> v))),
  forall (Test2: i1 < n),
  forall (aux_1: pointer),
  forall (Post15: aux_1 = (shift t i1)),
  forall (Pre2: (valid alloc aux_1)),
  forall (result0: Z),
  forall (Post17: result0 = (acc intP aux_1)),
  ((result0 = v -> ((0 <= i1 /\ i1 < n -> (acc intP (shift t i1)) = v)) /\
    ((i1 = n ->
      (forall (i:Z), (0 <= i /\ i < n -> (acc intP (shift t i)) <> v)))))) /\
  ((result0 <> v ->
    (forall (i:Z),
     (i = (i1 + 1) -> (0 <= i /\
      (forall (k:Z), (0 <= k /\ k < i -> (acc intP (shift t k)) <> v))) /\
      (Zwf 0 (n - i) (n - i1)))))).
Proof.
intuition.
subst ; auto.
assert (k<i1 \/ k=i1) ; [omega | intuition ].
apply (H0 k); auto with *.
subst; auto.
Save.

(* Why obligation from file "why/search.why", characters 184-557 *)
Lemma index_impl_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (Post2: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre5: Variant1 = (n - i1)),
  forall (Pre4: 0 <= i1 /\
                (forall (k:Z),
                 (0 <= k /\ k < i1 -> (acc intP (shift t k)) <> v))),
  forall (Test1: i1 >= n),
  ((0 <= i1 /\ i1 < n -> (acc intP (shift t i1)) = v)) /\
  ((i1 = n ->
    (forall (i:Z), (0 <= i /\ i < n -> (acc intP (shift t i)) <> v)))).
Proof.
intuition.
Save.

(* Why obligation from file "why/search.why", characters 233-374 *)
Lemma index_impl_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (Post2: i = 0),
  0 <= i /\ (forall (k:Z), (0 <= k /\ k < i -> (acc intP (shift t k)) <> v)).
Proof.
intuition.
subst; auto.
apply (H2 i0); intuition.
Save.

