(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.
Require Export Why.

Proof.
intros; subst Variant1; trivial.
Qed.

Proof.
destruct result0; intuition.
Qed.

Proof.
intuition.
Qed.

Proof.
destruct result0; intuition.
Qed.

Proof.
intuition.
Qed.

Proof.
destruct result1; intuition.
Qed.

Proof.
intuition.
Qed.
(* Why obligation from file "why/break.why", characters 155-166 *)
Lemma f1_impl_po_1 : 
  forall (Variant1: Z),
  forall (Pre3: Variant1 = 1),
  forall (Test2: 1 <> 0),
  True.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 101-171 *)
Lemma f1_impl_po_2 : 
  forall (Variant1: Z),
  forall (Pre3: Variant1 = 1),
  forall (Test2: 1 <> 0),
  forall (Post5: (Zwf 0 1 1)),
  (Zwf 0 1 Variant1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 211-213 *)
Lemma f1_impl_po_3 : 
  forall (result0: Z),
  forall (Post4: result0 = 12),
  result0 = 12.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 326-328 *)
Lemma f2_impl_po_1 : 
  forall (result: Z),
  forall (Post9: result = 10),
  0 <= result /\
  (forall (n:Z), (0 <= n -> ((n >= 0 -> True)) /\ ((n < 0 -> True)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 483-499 *)
Lemma f2_impl_po_2 : 
  forall (n: Z),
  forall (Variant1: Z),
  forall (n1: Z),
  forall (Pre3: Variant1 = n1),
  forall (Pre2: 0 <= n1),
  forall (Test4: n1 >= 0),
  forall (Test3: n1 = 0),
  forall (result1: Z),
  forall (Post3: result1 = (n1 + 1)),
  True.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 532-548 *)
Lemma f2_impl_po_3 : 
  forall (n: Z),
  forall (Variant1: Z),
  forall (n1: Z),
  forall (Pre3: Variant1 = n1),
  forall (Pre2: 0 <= n1),
  forall (Test4: n1 >= 0),
  forall (Test2: n1 <> 0),
  forall (result1: Z),
  forall (Post2: result1 = (n1 - 1)),
  0 <= result1 /\ (Zwf 0 result1 n1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 597-599 *)
Lemma f2_impl_po_4 : 
  forall (n: Z),
  forall (n1: Z),
  forall (result0: Z),
  forall (Post8: result0 = n1),
  result0 = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 711-713 *)
Lemma f3_impl_po_1 : 
  forall (result: Z),
  forall (Post9: result = 10),
  1 <= result /\
  (forall (n:Z), (1 <= n -> ((n >= 0 -> True)) /\ ((n < 0 -> True)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 868-884 *)
Lemma f3_impl_po_2 : 
  forall (n: Z),
  forall (Variant1: Z),
  forall (n1: Z),
  forall (Pre3: Variant1 = n1),
  forall (Pre2: 1 <= n1),
  forall (Test4: n1 >= 0),
  forall (Test3: n1 = 1),
  forall (result1: Z),
  forall (Post3: result1 = (n1 + 1)),
  True.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 917-933 *)
Lemma f3_impl_po_3 : 
  forall (n: Z),
  forall (Variant1: Z),
  forall (n1: Z),
  forall (Pre3: Variant1 = n1),
  forall (Pre2: 1 <= n1),
  forall (Test4: n1 >= 0),
  forall (Test2: n1 <> 1),
  forall (result1: Z),
  forall (Post2: result1 = (n1 - 1)),
  1 <= result1 /\ (Zwf 0 result1 n1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 982-984 *)
Lemma f3_impl_po_4 : 
  forall (n: Z),
  forall (n1: Z),
  forall (result0: Z),
  forall (Post8: result0 = n1),
  result0 = 2.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 1145-1146 *)
Lemma f4_impl_po_1 : 
  forall (result: Z),
  forall (Post1: result = 0),
  result <= 3 /\
  (forall (i:Z), (i <= 3 -> ((i < 10 -> True)) /\ ((i >= 10 -> True)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 1306-1322 *)
Lemma f4_impl_po_2 : 
  forall (i1: Z),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (Pre3: Variant1 = (10 - i2)),
  forall (Pre2: i2 <= 3),
  forall (Test4: i2 < 10),
  forall (result2: Z),
  forall (Post6: result2 = (i2 + 1)),
  result2 <= 3 /\ (Zwf 0 (10 - result2) (10 - i2)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 1248-1322 *)
Lemma f4_impl_po_3 : 
  forall (i1: Z),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (Pre3: Variant1 = (10 - i2)),
  forall (Pre2: i2 <= 3),
  forall (Test4: i2 < 10),
  True.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/break.why", characters 1382-1384 *)
Lemma f4_impl_po_4 : 
  forall (i1: Z),
  forall (result0: Z),
  forall (Post9: result0 = i1),
  result0 = 3.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

