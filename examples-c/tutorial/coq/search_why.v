(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export search_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_1 : 
  forall (t: ((pointer) Z0)),
  forall (n: Z),
  forall (v: Z),
  forall (Int_Z0: ((memory) Z Z0)),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "search.c", line 1, characters 14-35 *)
                (valid_range alloc t 0 (n - 1))),
  (* File "search.c", line 8, characters 17-65 *) (0 <= 0 /\
  (forall (k:Z), (0 <= k /\ k < 0 -> (acc Int_Z0 (shift t k)) <> v))).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_2 : 
  forall (t: ((pointer) Z0)),
  forall (n: Z),
  forall (v: Z),
  forall (Int_Z0: ((memory) Z Z0)),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "search.c", line 1, characters 14-35 *)
                (valid_range alloc t 0 (n - 1))),
  forall (HW_2: (* File "search.c", line 8, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc Int_Z0 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_3: (* File "search.c", line 8, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc Int_Z0 (shift t k)) <> v)))),
  forall (HW_4: i < n),
  forall (result: ((pointer) Z0)),
  forall (HW_5: result = (shift t i)),
  (valid alloc result).
Proof.
intuition.
subst.
auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_3 : 
  forall (t: ((pointer) Z0)),
  forall (n: Z),
  forall (v: Z),
  forall (Int_Z0: ((memory) Z Z0)),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "search.c", line 1, characters 14-35 *)
                (valid_range alloc t 0 (n - 1))),
  forall (HW_2: (* File "search.c", line 8, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc Int_Z0 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_3: (* File "search.c", line 8, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc Int_Z0 (shift t k)) <> v)))),
  forall (HW_4: i < n),
  forall (result: ((pointer) Z0)),
  forall (HW_5: result = (shift t i)),
  forall (HW_6: (valid alloc result)),
  forall (result0: Z),
  forall (HW_7: result0 = (acc Int_Z0 result)),
  forall (HW_8: result0 = v),
  (* File "search.c", line 3, characters 5-106 *)
  (((0 <= i /\ i < n -> (acc Int_Z0 (shift t i)) = v)) /\
  ((i = n ->
    (forall (i:Z), (0 <= i /\ i < n -> (acc Int_Z0 (shift t i)) <> v))))).
Proof.
intuition.
assert (k<i1 \/ k=i1).
omega.
intuition.
apply (H0 k); intuition.
apply Test2.
subst; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_4 : 
  forall (t: ((pointer) Z0)),
  forall (n: Z),
  forall (v: Z),
  forall (Int_Z0: ((memory) Z Z0)),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "search.c", line 1, characters 14-35 *)
                (valid_range alloc t 0 (n - 1))),
  forall (HW_2: (* File "search.c", line 8, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc Int_Z0 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_3: (* File "search.c", line 8, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc Int_Z0 (shift t k)) <> v)))),
  forall (HW_4: i < n),
  forall (result: ((pointer) Z0)),
  forall (HW_5: result = (shift t i)),
  forall (HW_6: (valid alloc result)),
  forall (result0: Z),
  forall (HW_7: result0 = (acc Int_Z0 result)),
  forall (HW_9: result0 <> v),
  forall (i0: Z),
  forall (HW_10: i0 = (i + 1)),
  (* File "search.c", line 8, characters 17-65 *) (0 <= i0 /\
  (forall (k:Z), (0 <= k /\ k < i0 -> (acc Int_Z0 (shift t k)) <> v))) /\
  (Zwf 0 (n - i0) (n - i)).
Proof.
intuition.
apply H0 with i0.
omega.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_5 : 
  forall (t: ((pointer) Z0)),
  forall (n: Z),
  forall (v: Z),
  forall (Int_Z0: ((memory) Z Z0)),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "search.c", line 1, characters 14-35 *)
                (valid_range alloc t 0 (n - 1))),
  forall (HW_2: (* File "search.c", line 8, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc Int_Z0 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_3: (* File "search.c", line 8, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc Int_Z0 (shift t k)) <> v)))),
  forall (HW_11: i >= n),
  (* File "search.c", line 3, characters 5-106 *)
  (((0 <= i /\ i < n -> (acc Int_Z0 (shift t i)) = v)) /\
  ((i = n ->
    (forall (i:Z), (0 <= i /\ i < n -> (acc Int_Z0 (shift t i)) <> v))))).
Proof.
intuition.
Save.

