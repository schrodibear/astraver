(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.




Proof.
intuition.
Qed.

Proof.
intuition.
Qed.



(* Why obligation from file "why/passing.why", characters 159-187 *)
Lemma f_impl_po_1 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (t: pointer),
  forall (Pre4: (valid_index alloc x 0) /\ (valid_range alloc t 0 1)),
  forall (caduceus_1: pointer),
  forall (Post3: caduceus_1 = (shift x 0)),
  (valid alloc caduceus_1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/passing.why", characters 124-187 *)
Lemma f_impl_po_2 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (Pre4: (valid_index alloc x 0) /\ (valid_range alloc t 0 1)),
  forall (caduceus_1: pointer),
  forall (Post3: caduceus_1 = (shift x 0)),
  forall (Pre3: (valid alloc caduceus_1)),
  forall (intP0: ((memory) Z)),
  forall (Post5: intP0 = (upd intP caduceus_1 1)),
  (acc intP0 (shift x 0)) = 1 /\
  (assigns alloc intP intP0 (pointer_loc (shift x 0))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/passing.why", characters 414-460 *)
Lemma g2_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (r: pointer),
  forall (t: pointer),
  forall (Pre4: (valid alloc r) /\ (valid_range alloc t 0 1)),
  forall (intP0: ((memory) Z)),
  forall (Post4: (acc intP0 r) = 0 /\
                 (assigns alloc intP intP0 (pointer_loc r))),
  forall (Pre3: (valid alloc r)),
  forall (result0: Z),
  forall (Post2: result0 = (acc intP0 r)),
  result0 = 0.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/passing.why", characters 526-714 *)
Lemma g_impl_po_1 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (Pre4: (valid alloc x) /\ (valid_range alloc t 0 1)),
  forall (Pre3: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post3: intP0 = (upd intP x 0)),
  (acc intP0 x) = 0 /\ (assigns alloc intP intP0 (pointer_loc x)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/passing.why", characters 804-820 *)
Lemma main_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (t: pointer),
  forall (Pre4: (valid_range alloc t 0 1)),
  (valid_index alloc t 0) /\ (valid_range alloc t 0 1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

