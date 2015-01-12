(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require WhyFloat.

Axiom magic : False.
Tactic Definition Magic := Elim magic.

(* Why obligation from file "copy.c", characters 156-159 *)
Lemma copy_po_1 : 
  (n: Z)
  (t1: (array Z))
  (t2: (array Z))
  (Pre6: `(array_length t1) >= n` /\ `(array_length t2) >= n`)
  (i: Z)
  (Post5: i = n)
  (Variant1: Z)
  (i1: Z)
  (t2_0: (array Z))
  (Pre5: Variant1 = i1)
  (Pre4: `(array_length t2_0) >= n` /\ `i1 <= n` /\
         ((k:Z) (`i1 <= k` /\ `k < n` -> `(access t2_0 k) = (access t1 k)`)))
  (Test2: true = true)
  (c_aux_2: Z)
  (Post2: c_aux_2 = i1)
  (i2: Z)
  (Post1: i2 = `i1 - 1`)
  ((`c_aux_2 > 0` ->
    ((result:Z)
     (result = i2 ->
      (((t2:(array Z))
        (t2 = (store t2_0 result (access t1 i2)) ->
         (`(array_length t2) >= n` /\ `i2 <= n` /\
         ((k:Z) (`i2 <= k` /\ `k < n` -> `(access t2 k) = (access t1 k)`))) /\
         (Zwf `0` i2 i1))) /\
      `0 <= result` /\ `result < (array_length t2_0)`) /\ `0 <= i2` /\
      `i2 < (array_length t1)`)))) /\
  ((`c_aux_2 <= 0` ->
    ((k:Z) (`0 <= k` /\ `k < n` -> `(access t2_0 k) = (access t1 k)`)))).
Proof.
Intuition.
Subst t0; Trivial.
Assert k=i2 \/ `i2<k`. Omega. Intuition.
Subst result k t0.
AccessSame.
Subst result t0; AccessOther.
Apply H4; Omega.
Save.

(* Why obligation from file "copy.c", characters 185-281 *)
Lemma copy_po_2 : 
  (n: Z)
  (t1: (array Z))
  (t2: (array Z))
  (Pre6: `(array_length t1) >= n` /\ `(array_length t2) >= n`)
  (i: Z)
  (Post5: i = n)
  `(array_length t2) >= n` /\ `i <= n` /\
  ((k:Z) (`i <= k` /\ `k < n` -> `(access t2 k) = (access t1 k)`)).
Proof.
Auto with *.
Save.
