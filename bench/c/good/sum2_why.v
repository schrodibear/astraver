
Require Import caduceus_why.


(* Why obligation from file "sum2.why", characters 262-266 *)
Lemma test1_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (i: Z),
  forall (Post5: i = (any_int tt)),
  forall (s: Z),
  forall (Post4: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (s1: Z),
  forall (Pre3: Variant1 = 0),
  forall (Test2: i1 < n),
  forall (s2: Z),
  forall (Post2: s2 = (s1 + (acc intP (shift t i1)))),
  (Zwf 0 0 0).
Proof.
(* FILL PROOF HERE *)
Admitted.

(* Why obligation from file "sum2.why", characters 147-274 *)
Lemma test1_po_2 : 
  forall (n: Z),
  forall (i: Z),
  forall (Post5: i = (any_int tt)),
  forall (s: Z),
  forall (Post4: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (Pre3: Variant1 = 0),
  forall (Test2: i1 < n),
  forall (Post6: (Zwf 0 0 0)),
  (Zwf 0 0 Variant1).
Proof.
intuition; subst; auto with *.
Save.

(* Why obligation from file "sum2.why", characters 485-566 *)
Lemma test2_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (i: Z),
  forall (Post4: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre3: Variant1 = 0),
  forall (Test2: i1 < n),
  forall (intP1: ((memory) Z)),
  forall (Post2: intP1 = (upd intP0 (shift t i1)
                          ((acc intP0 (shift t i1)) + 1))),
  (Zwf 0 0 0).
Proof.
Admitted.



(* Why obligation from file "sum2.why", characters 424-574 *)
Lemma test2_po_2 : 
  forall (n: Z),
  forall (i: Z),
  forall (Post4: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (Pre3: Variant1 = 0),
  forall (Test2: i1 < n),
  forall (Post5: (Zwf 0 0 0)),
  (Zwf 0 0 Variant1).
Proof.
intuition; subst; auto with *.
Save.


