(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.
Require Export Why.

(* Why obligation from file "why/break.why", characters 94-160 *)
Lemma f1_impl_po_1 : 
  forall (Variant1: Z),
  forall (Pre3: Variant1 = 1),
  forall (Test2: 1 <> 0),
  forall (Post4: (Zwf 0 1 1)),
  (Zwf 0 1 Variant1).
Proof.
intuition;subst;auto.
Save.

(* Why obligation from file "why/break.why", characters 498-504 *)
Lemma f2_impl_po_1 : 
  forall (n: Z),
  forall (Post7: n = 10),
  forall (Variant1: Z),
  forall (n1: Z),
  forall (Pre3: Variant1 = n1),
  forall (Pre2: 0 <= n1),
  forall (Test4: n1 >= 0),
  forall (Test3: n1 = 0),
  forall (n2: Z),
  forall (Post4: n2 = (n1 + 1)),
  (forall (result:unit),
   (result = tt -> (forall (result:Z), (result = n2 -> result = 1)))).
Proof.
intuition.
Save.

(* Why obligation from file "why/break.why", characters 525-545 *)
Lemma f2_impl_po_2 : 
  forall (n: Z),
  forall (Post7: n = 10),
  forall (Variant1: Z),
  forall (n1: Z),
  forall (Pre3: Variant1 = n1),
  forall (Pre2: 0 <= n1),
  forall (Test4: n1 >= 0),
  forall (Test2: n1 <> 0),
  forall (n2: Z),
  forall (Post3: n2 = (n1 - 1)),
  0 <= n2 /\ (Zwf 0 n2 n1).
Proof.
intuition.
Save.

(* Why obligation from file "why/break.why", characters 364-552 *)
Lemma f2_impl_po_3 : 
  forall (n: Z),
  forall (Post7: n = 10),
  forall (Variant1: Z),
  forall (n1: Z),
  forall (Pre3: Variant1 = n1),
  forall (Pre2: 0 <= n1),
  forall (Test1: n1 < 0),
  (forall (result:Z), (result = n1 -> result = 1)).
Proof.
intuition.
Save.

(* Why obligation from file "why/break.why", characters 406-417 *)
Lemma f2_impl_po_4 : 
  forall (n: Z),
  forall (Post7: n = 10),
  0 <= n.
Proof.
intuition.
Save.

(* Why obligation from file "why/break.why", characters 900-906 *)
Lemma f3_impl_po_1 : 
  forall (n: Z),
  forall (Post7: n = 10),
  forall (Variant1: Z),
  forall (n1: Z),
  forall (Pre3: Variant1 = n1),
  forall (Pre2: 1 <= n1),
  forall (Test4: n1 >= 0),
  forall (Test3: n1 = 1),
  forall (n2: Z),
  forall (Post4: n2 = (n1 + 1)),
  (forall (result:unit),
   (result = tt -> (forall (result:Z), (result = n2 -> result = 2)))).
Proof.
intuition.
Save.

(* Why obligation from file "why/break.why", characters 927-947 *)
Lemma f3_impl_po_2 : 
  forall (n: Z),
  forall (Post7: n = 10),
  forall (Variant1: Z),
  forall (n1: Z),
  forall (Pre3: Variant1 = n1),
  forall (Pre2: 1 <= n1),
  forall (Test4: n1 >= 0),
  forall (Test2: n1 <> 1),
  forall (n2: Z),
  forall (Post3: n2 = (n1 - 1)),
  1 <= n2 /\ (Zwf 0 n2 n1).
Proof.
intuition.
Save.

(* Why obligation from file "why/break.why", characters 766-954 *)
Lemma f3_impl_po_3 : 
  forall (n: Z),
  forall (Post7: n = 10),
  forall (Variant1: Z),
  forall (n1: Z),
  forall (Pre3: Variant1 = n1),
  forall (Pre2: 1 <= n1),
  forall (Test1: n1 < 0),
  (forall (result:Z), (result = n1 -> result = 2)).
Proof.
intuition.
Save.

(* Why obligation from file "why/break.why", characters 808-819 *)
Lemma f3_impl_po_4 : 
  forall (n: Z),
  forall (Post7: n = 10),
  1 <= n.
Proof.
intuition.
Save.

(* Why obligation from file "why/break.why", characters 1304-1310 *)
Lemma f4_impl_po_1 : 
  forall (i: Z),
  forall (Post8: i = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (Pre3: Variant1 = (10 - i2)),
  forall (Pre2: i2 <= 3),
  forall (Test4: i2 < 10),
  forall (Test3: i2 = 3),
  (forall (result:unit),
   (result = tt -> (forall (result:Z), (result = i2 -> result = 3)))).
Proof.
intuition.
Save.

(* Why obligation from file "why/break.why", characters 1321-1321 *)
Lemma f4_impl_po_2 : 
  forall (i: Z),
  forall (Post8: i = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (Pre3: Variant1 = (10 - i2)),
  forall (Pre2: i2 <= 3),
  forall (Test4: i2 < 10),
  forall (Test2: i2 <> 3),
  forall (result2: unit),
  forall (Post4: result2 = tt),
  (forall (i:Z), (i = (i2 + 1) -> i <= 3 /\ (Zwf 0 (10 - i) (10 - i2)))).
Proof.
intuition.
Save.

(* Why obligation from file "why/break.why", characters 1191-1362 *)
Lemma f4_impl_po_3 : 
  forall (i: Z),
  forall (Post8: i = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (Pre3: Variant1 = (10 - i2)),
  forall (Pre2: i2 <= 3),
  forall (Test1: i2 >= 10),
  (forall (result:Z), (result = i2 -> result = 3)).
Proof.
intuition.
Save.

(* Why obligation from file "why/break.why", characters 1235-1246 *)
Lemma f4_impl_po_4 : 
  forall (i: Z),
  forall (Post8: i = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  i1 <= 3.
Proof.
intuition.
Save.

