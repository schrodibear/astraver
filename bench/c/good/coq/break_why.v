(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export break_spec_why.
Require Export Why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f1_impl_po_1 : 
  (* File "break.c", line 8, characters 17-22 *) True.
Proof.
intuition;subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f1_impl_po_2 : 
  forall (HW_2: (* File "break.c", line 8, characters 17-22 *) True),
  forall (HW_3: 1 <> 0),
  (* File "break.c", line 5, characters 13-26 *) 12 = 12.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f1_impl_po_3 : 
  forall (HW_2: (* File "break.c", line 8, characters 17-22 *) True),
  forall (HW_4: 1 = 0),
  (* File "break.c", line 5, characters 13-26 *) 12 = 12.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_1 : 
  (* File "break.c", line 18, characters 17-23 *) 0 <= 10.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_2 : 
  forall (HW_1: (* File "break.c", line 18, characters 17-23 *) 0 <= 10),
  forall (n: Z),
  forall (HW_2: (* File "break.c", line 18, characters 17-23 *) 0 <= n),
  forall (HW_3: n >= 0),
  forall (HW_4: n = 0),
  forall (n0: Z),
  forall (HW_5: n0 = (n + 1)),
  (* File "break.c", line 13, characters 13-25 *) n0 = 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_3 : 
  forall (HW_1: (* File "break.c", line 18, characters 17-23 *) 0 <= 10),
  forall (n: Z),
  forall (HW_2: (* File "break.c", line 18, characters 17-23 *) 0 <= n),
  forall (HW_3: n >= 0),
  forall (HW_6: n <> 0),
  forall (n0: Z),
  forall (HW_7: n0 = (n - 1)),
  (* File "break.c", line 18, characters 17-23 *) 0 <= n0 /\ (Zwf 0 n0 n).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_4 : 
  forall (HW_1: (* File "break.c", line 18, characters 17-23 *) 0 <= 10),
  forall (n: Z),
  forall (HW_2: (* File "break.c", line 18, characters 17-23 *) 0 <= n),
  forall (HW_8: n < 0),
  (* File "break.c", line 13, characters 13-25 *) n = 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f3_impl_po_1 : 
  (* File "break.c", line 31, characters 17-23 *) 1 <= 10.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f3_impl_po_2 : 
  forall (HW_1: (* File "break.c", line 31, characters 17-23 *) 1 <= 10),
  forall (n: Z),
  forall (HW_2: (* File "break.c", line 31, characters 17-23 *) 1 <= n),
  forall (HW_3: n >= 0),
  forall (HW_4: n = 1),
  forall (n0: Z),
  forall (HW_5: n0 = (n + 1)),
  (* File "break.c", line 27, characters 13-25 *) n0 = 2.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f3_impl_po_3 : 
  forall (HW_1: (* File "break.c", line 31, characters 17-23 *) 1 <= 10),
  forall (n: Z),
  forall (HW_2: (* File "break.c", line 31, characters 17-23 *) 1 <= n),
  forall (HW_3: n >= 0),
  forall (HW_6: n <> 1),
  forall (n0: Z),
  forall (HW_7: n0 = (n - 1)),
  (* File "break.c", line 31, characters 17-23 *) 1 <= n0 /\ (Zwf 0 n0 n).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f3_impl_po_4 : 
  forall (HW_1: (* File "break.c", line 31, characters 17-23 *) 1 <= 10),
  forall (n: Z),
  forall (HW_2: (* File "break.c", line 31, characters 17-23 *) 1 <= n),
  forall (HW_8: n < 0),
  (* File "break.c", line 27, characters 13-25 *) n = 2.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_1 : 
  forall (i: Z),
  forall (HW_1: i = 0),
  (* File "break.c", line 43, characters 17-23 *) i <= 3.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_2 : 
  forall (i: Z),
  forall (HW_1: i = 0),
  forall (HW_2: (* File "break.c", line 43, characters 17-23 *) i <= 3),
  forall (i0: Z),
  forall (HW_3: (* File "break.c", line 43, characters 17-23 *) i0 <= 3),
  forall (HW_4: i0 < 10),
  forall (HW_6: i0 <> 3),
  forall (i1: Z),
  forall (HW_7: i1 = (i0 + 1)),
  (* File "break.c", line 43, characters 17-23 *) i1 <= 3 /\
  (Zwf 0 (10 - i1) (10 - i0)).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_3 : 
  forall (i: Z),
  forall (HW_1: i = 0),
  forall (HW_2: (* File "break.c", line 43, characters 17-23 *) i <= 3),
  forall (i0: Z),
  forall (HW_3: (* File "break.c", line 43, characters 17-23 *) i0 <= 3),
  forall (HW_8: i0 >= 10),
  (* File "break.c", line 39, characters 13-25 *) i0 = 3.
Proof.
intuition.
Save.
