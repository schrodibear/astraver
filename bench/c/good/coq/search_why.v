(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/search.why", characters 162-208 *)
Lemma index2_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (Post3: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre5: Variant1 = (n - i1)),
  forall (Pre4: 0 <= i1 /\
                (forall (k:Z),
                 (0 <= k /\ k < i1 -> (acc intP (shift t k)) <> v))),
  forall (Test2: true = true),
  forall (caduceus_2: Z),
  forall (Post1: caduceus_2 = i1),
  forall (result0: bool),
  forall (Post16: (if result0 then caduceus_2 < n else caduceus_2 >= n)),
  (if result0
   then (forall (result:pointer),
         (result = (shift t i1) ->
          (forall (result0:Z),
           (result0 = (acc intP result) ->
            ((result0 = v ->
              (0 <= i1 /\ i1 < n -> (acc intP (shift t i1)) = v))) /\
            ((result0 <> v ->
              (forall (i:Z),
               (i = (i1 + 1) -> (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intP (shift t k)) <> v))) /\
                (Zwf 0 (n - i) (n - i1)))))))) /\
          (valid alloc result)))
   else (0 <= n /\ n < n -> (acc intP (shift t n)) = v)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/search.why", characters 238-382 *)
Lemma index2_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (Post3: i = 0),
  0 <= i /\ (forall (k:Z), (0 <= k /\ k < i -> (acc intP (shift t k)) <> v)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/search.why", characters 907-953 *)
Lemma index_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (Post3: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre5: Variant1 = (n - i1)),
  forall (Pre4: 0 <= i1 /\
                (forall (k:Z),
                 (0 <= k /\ k < i1 -> (acc intP (shift t k)) <> v))),
  forall (Test2: true = true),
  forall (caduceus_2: Z),
  forall (Post1: caduceus_2 = i1),
  forall (result0: bool),
  forall (Post15: (if result0 then caduceus_2 < n else caduceus_2 >= n)),
  (if result0
   then (forall (result:pointer),
         (result = (shift t i1) ->
          (forall (result0:Z),
           (result0 = (acc intP result) ->
            ((result0 = v ->
              ((0 <= i1 /\ i1 < n -> (acc intP (shift t i1)) = v)) /\
              ((i1 = n ->
                (forall (i:Z),
                 (0 <= i /\ i < n -> (acc intP (shift t i)) <> v)))))) /\
            ((result0 <> v ->
              (forall (i:Z),
               (i = (i1 + 1) -> (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intP (shift t k)) <> v))) /\
                (Zwf 0 (n - i) (n - i1)))))))) /\
          (valid alloc result)))
   else ((0 <= i1 /\ i1 < n -> (acc intP (shift t i1)) = v)) /\
   ((i1 = n ->
     (forall (i:Z), (0 <= i /\ i < n -> (acc intP (shift t i)) <> v))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/search.why", characters 983-1127 *)
Lemma index_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (Post3: i = 0),
  0 <= i /\ (forall (k:Z), (0 <= k /\ k < i -> (acc intP (shift t k)) <> v)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

