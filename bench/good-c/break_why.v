(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

(* Why obligation from file "good-c/break.c", characters 34-82 *)
Lemma f1_po_1 : 
  (Variant1: Z)
  (Pre3: Variant1 = `1`)
  (Test2: `1 <> 0`)
  (Post2: (Zwf `0` `1` `1`))
  (Zwf `0` `1` Variant1).
Proof.
Intros; Subst Variant1; Trivial.
Save.

(* Why obligation from file "good-c/break.c", characters 227-233 *)
Lemma f2_po_1 : 
  (result: Z)
  (Post4: result = `10`)
  (Variant1: Z)
  (n0: Z)
  (Pre3: Variant1 = n0)
  (Pre2: `0 <= n0`)
  (Test4: `n0 >= 0`)
  (Test3: `n0 = 0`)
  (n1: Z)
  (Post1: n1 = `n0 + 1`)
  `n1 = 1`.
Proof.
Intuition.
Save.

(* Why obligation from file "good-c/break.c", characters 208-235 *)
Lemma f2_po_2 : 
  (result: Z)
  (Post4: result = `10`)
  (Variant1: Z)
  (n0: Z)
  (Pre3: Variant1 = n0)
  (Pre2: `0 <= n0`)
  (Test4: `n0 >= 0`)
  (Test2: `n0 <> 0`)
  ((n:Z) (n = `n0 - 1` -> `0 <= n` /\ (Zwf `0` n n0))).
Proof.
Unfold Zwf; Intuition.
Save.

(* Why obligation from file "good-c/break.c", characters 182-188 *)
Lemma f2_po_3 : 
  (result: Z)
  (Post4: result = `10`)
  `0 <= result`.
Proof.
Unfold Zwf; Intuition.
Save.

(* Why obligation from file "good-c/break.c", characters 147-248 *)
Lemma f2_po_4 : 
  (result: Z)
  (Post4: result = `10`)
  (n0: Z)
  (Post3: `0 <= n0` /\ `n0 < 0`)
  `n0 = 1`.
Proof.
Intros; Omega.
Save.


(* Why obligation from file "good-c/break.c", characters 395-401 *)
Lemma f3_po_1 : 
  (result: Z)
  (Post4: result = `10`)
  (Variant1: Z)
  (n0: Z)
  (Pre3: Variant1 = n0)
  (Pre2: `1 <= n0`)
  (Test4: `n0 >= 0`)
  (Test3: `n0 = 1`)
  (n1: Z)
  (Post1: n1 = `n0 + 1`)
  `n1 = 2`.
Proof.
Intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "good-c/break.c", characters 376-403 *)
Lemma f3_po_2 : 
  (result: Z)
  (Post4: result = `10`)
  (Variant1: Z)
  (n0: Z)
  (Pre3: Variant1 = n0)
  (Pre2: `1 <= n0`)
  (Test4: `n0 >= 0`)
  (Test2: `n0 <> 1`)
  ((n:Z) (n = `n0 - 1` -> `1 <= n` /\ (Zwf `0` n n0))).
Proof.
Intuition.
Unfold Zwf; Omega.
Save.

(* Why obligation from file "good-c/break.c", characters 350-356 *)
Lemma f3_po_3 : 
  (result: Z)
  (Post4: result = `10`)
  `1 <= result`.
Proof.
Intuition.
Save.

(* Why obligation from file "good-c/break.c", characters 315-416 *)
Lemma f3_po_4 : 
  (result: Z)
  (Post4: result = `10`)
  (n0: Z)
  (Post3: `1 <= n0` /\ `n0 < 0`)
  `n0 = 2`.
Proof.
Intuition.
Save.


(* Why obligation from file "good-c/break.c", characters 576-594 *)
Lemma f4_po_1 : 
  (result: Z)
  (Post4: result = `0`)
  (i0: Z)
  (Post1: i0 = `0`)
  (Variant1: Z)
  (i1: Z)
  (Pre3: Variant1 = `10 - i1`)
  (Pre2: `i1 <= 3`)
  (Test4: `i1 < 10`)
  (Test2: `i1 <> 3`)
  ((i:Z) (i = `i1 + 1` -> `i <= 3` /\ (Zwf `0` `10 - i` `10 - i1`))).
Proof.
Intuition.
Unfold Zwf; Omega.
Save.

(* Why obligation from file "good-c/break.c", characters 539-545 *)
Lemma f4_po_2 : 
  (result: Z)
  (Post4: result = `0`)
  (i0: Z)
  (Post1: i0 = `0`)
  `i0 <= 3`.
Proof.
Intuition.
Save.

(* Why obligation from file "good-c/break.c", characters 495-600 *)
Lemma f4_po_3 : 
  (result: Z)
  (Post4: result = `0`)
  (i0: Z)
  (Post1: i0 = `0`)
  (i1: Z)
  (Post3: `i1 <= 3` /\ `i1 >= 10`)
  `i1 = 3`.
Proof.
Intuition.
Save.


