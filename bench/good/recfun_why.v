(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.

(* Why obligation from file "recfun.mlw", characters 140-141 *)
Lemma f1_po_1 : 
  forall (x: Z),
  forall (Pre4: x >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (Pre3: Variant1 = x0),
  forall (Pre2: x0 >= 0),
  forall (Test1: x0 <= 0),
  forall (result0: Z),
  forall (Post1: result0 = x0),
  result0 = 0.
Proof.
intros; omega.
Qed.

Proof.
intros; unfold Zwf; omega.
Qed.

Proof.
intros; omega.
Qed.






(* Why obligation from file "recfun.mlw", characters 300-311 *)
Lemma f2_po_1 : 
  forall (x: Z),
  forall (Pre8: x >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = x0),
  forall (Pre6: x0 >= 0),
  forall (Test2: x0 > 0),
  forall (result0: Z),
  forall (Post2: result0 = (x0 - 1)),
  (forall (x:Z), (x = 0 -> x = 0)) /\ result0 >= 0.
Proof.
intros; omega.
Qed.

(* Why obligation from file "recfun.mlw", characters 267-337 *)
Lemma f2_po_2 : 
  forall (x: Z),
  forall (Pre8: x >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = x0),
  forall (Pre6: x0 >= 0),
  forall (Test2: x0 > 0),
  forall (x1: Z),
  forall (Pre5: x1 >= 0),
  forall (result1: unit),
  forall (Post3: result1 = tt),
  forall (Pre3: x1 >= 0),
  forall (Pre4: x1 >= 0),
  (Zwf 0 x1 Variant1).
Proof.
intros; unfold Zwf; omega.
Qed.

(* Why obligation from file "recfun.mlw", characters 326-326 *)
Lemma f2_po_3 : 
  forall (x: Z),
  forall (Pre8: x >= 0),
  forall (Variant1: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = x0),
  forall (Pre6: x0 >= 0),
  forall (Test1: x0 <= 0),
  forall (result0: unit),
  forall (Post1: result0 = tt),
  x0 = 0.
Proof.
intros; omega.
Qed.





(* Why obligation from file "recfun.mlw", characters 459-470 *)
Lemma f3_po_1 : 
  forall (a: Z),
  forall (Pre8: a >= 0),
  forall (Variant1: Z),
  forall (a0: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = a0),
  forall (Pre6: a0 >= 0),
  forall (Test2: a0 > 0),
  forall (result0: Z),
  forall (Post2: result0 = (x0 + 1)),
  (forall (x:Z), (x = (result0 + (a0 - 1)) -> x = (x0 + a0))) /\ (a0 - 1) >=
  0.
Proof.
intros; omega.
Qed.

(* Why obligation from file "recfun.mlw", characters 427-502 *)
Lemma f3_po_2 : 
  forall (a: Z),
  forall (Pre8: a >= 0),
  forall (Variant1: Z),
  forall (a0: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = a0),
  forall (Pre6: a0 >= 0),
  forall (Test2: a0 > 0),
  forall (x1: Z),
  forall (Pre5: (a0 - 1) >= 0),
  forall (result1: Z),
  forall (Post3: result1 = (a0 - 1)),
  forall (Pre3: (a0 - 1) >= 0),
  forall (Pre4: (a0 - 1) >= 0),
  (Zwf 0 result1 Variant1).
Proof.
intros; unfold Zwf; omega.
Qed.

(* Why obligation from file "recfun.mlw", characters 429-435 *)
Lemma f3_po_3 : 
  forall (a: Z),
  forall (Pre8: a >= 0),
  forall (Variant1: Z),
  forall (a0: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = a0),
  forall (Pre6: a0 >= 0),
  forall (Test2: a0 > 0),
  forall (x1: Z),
  forall (Pre5: (a0 - 1) >= 0),
  forall (result1: Z),
  forall (Post3: result1 = (a0 - 1)),
  forall (Pre3: (a0 - 1) >= 0),
  forall (Pre4: (a0 - 1) >= 0),
  result1 >= 0.
Proof.
intros; omega.
Qed.

(* Why obligation from file "recfun.mlw", characters 486-486 *)
Lemma f3_po_4 : 
  forall (a: Z),
  forall (Pre8: a >= 0),
  forall (Variant1: Z),
  forall (a0: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = a0),
  forall (Pre6: a0 >= 0),
  forall (Test1: a0 <= 0),
  forall (result0: unit),
  forall (Post1: result0 = tt),
  x0 = (x0 + a0).
Proof.
intros; omega.
Qed.





(* Why obligation from file "recfun.mlw", characters 640-651 *)
Lemma f4_po_1 : 
  forall (a: Z),
  forall (Pre8: a >= 0),
  forall (Variant1: Z),
  forall (a0: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = a0),
  forall (Pre6: a0 >= 0),
  forall (Test2: a0 > 0),
  forall (result0: Z),
  forall (Post2: result0 = (x0 + 1)),
  (forall (result:Z),
   (result = (a0 - 1) ->
    (forall (x:Z), (x = (result0 + result) -> x = (x0 + a0))) /\ result >= 0)).
Proof.
intros; omega.
Qed.

(* Why obligation from file "recfun.mlw", characters 604-695 *)
Lemma f4_po_2 : 
  forall (a: Z),
  forall (Pre8: a >= 0),
  forall (Variant1: Z),
  forall (a0: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = a0),
  forall (Pre6: a0 >= 0),
  forall (Test2: a0 > 0),
  forall (x1: Z),
  forall (a1: Z),
  forall (Pre5: a1 >= 0),
  forall (Pre3: a1 >= 0),
  forall (Pre4: a1 >= 0),
  (Zwf 0 a1 Variant1).
Proof.
intros; unfold Zwf; omega.
Qed.

(* Why obligation from file "recfun.mlw", characters 676-676 *)
Lemma f4_po_3 : 
  forall (a: Z),
  forall (Pre8: a >= 0),
  forall (Variant1: Z),
  forall (a0: Z),
  forall (x0: Z),
  forall (Pre7: Variant1 = a0),
  forall (Pre6: a0 >= 0),
  forall (Test1: a0 <= 0),
  forall (result0: unit),
  forall (Post1: result0 = tt),
  x0 = (x0 + a0).
Proof.
intros; omega.
Qed.

Proof.
intros; omega.
Qed.





