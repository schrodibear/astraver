(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Import WhyFloat.

Axiom magic : False.
Ltac Magic := elim magic.

(* Why obligation from file "copy.c", characters 156-159 *)
Lemma copy_po_1 : 
  forall (n: Z),
  forall (t1: (array Z)),
  forall (t2: (array Z)),
  forall (Pre6: (array_length t1) >= n /\ (array_length t2) >= n),
  forall (i: Z),
  forall (Post5: i = n),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (t2_0: (array Z)),
  forall (Pre5: Variant1 = i1),
  forall (Pre4: (array_length t2_0) >= n /\ i1 <= n /\
                (forall (k:Z),
                 (i1 <= k /\ k < n -> (access t2_0 k) = (access t1 k)))),
  forall (Test2: true = true),
  forall (c_aux_2: Z),
  forall (Post2: c_aux_2 = i1),
  forall (i2: Z),
  forall (Post1: i2 = (i1 - 1)),
  ((c_aux_2 > 0 ->
    (forall (result:Z),
     (result = i2 ->
      ((forall (t2:(array Z)),
        (t2 = (store t2_0 result (access t1 i2)) -> ((array_length t2) >=
         n /\ i2 <= n /\
         (forall (k:Z), (i2 <= k /\ k < n -> (access t2 k) = (access t1 k)))) /\
         (Zwf 0 i2 i1))) /\
      0 <= result /\ result < (array_length t2_0)) /\ 0 <= i2 /\ i2 <
      (array_length t1))))) /\
  ((c_aux_2 <= 0 ->
    (forall (k:Z), (0 <= k /\ k < n -> (access t2_0 k) = (access t1 k))))).
Proof.
intuition.
subst t0; trivial.
assert (k = i2 \/ (i2 < k)%Z).
 omega.
 intuition.
subst result k t0.
AccessSame.
subst result t0; AccessOther.
apply H4; omega.
Qed.

(* Why obligation from file "copy.c", characters 185-281 *)
Lemma copy_po_2 : 
  forall (n: Z),
  forall (t1: (array Z)),
  forall (t2: (array Z)),
  forall (Pre6: (array_length t1) >= n /\ (array_length t2) >= n),
  forall (i: Z),
  forall (Post5: i = n),
  (array_length t2) >= n /\ i <= n /\
  (forall (k:Z), (i <= k /\ k < n -> (access t2 k) = (access t1 k))).
Proof.
auto with *.
Qed.

