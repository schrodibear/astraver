(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.


(* ----------- PRELIMINAIRES ------------- *)
(* dÃ©finition et propriÃ©tÃ©s de    *)
Require Import Omega.
Require Import ZArithRing.

Ltac omega' := abstract omega.

Set Implicit Arguments.
Unset Strict Implicit.

(* Induction pour vÃ©rifier qu'on est le maximum *)
Inductive Maximize (t:array Z) (n m:Z) : Z -> Prop :=
    Maxim_cons :
      forall k:Z,
        ((k <= n)%Z -> (access t k <= m)%Z) ->
        ((k < n)%Z -> Maximize t n m (k + 1)%Z) -> Maximize t n m k.

(* Signification  de ce prÃ©dicat: *)
Lemma Maximize_ext1 :
 forall (t:array Z) (n m k i:Z),
   Maximize t n m k -> (k <= i <= n)%Z -> (access t i <= m)%Z.
  Proof.
  intros t n m k i H1; elim H1; auto.
  intros k0 H2 H3 HR H4; case (Z_eq_dec k0 i).
   intros H; rewrite <- H; apply H2; omega'.
   intros; apply HR; omega'.
Qed.

Lemma Maximize_ext2 :
 forall (t:array Z) (n m k:Z),
   (forall i:Z, (k <= i <= n)%Z -> (access t i <= m)%Z) ->
   Maximize t n m k.
  Proof.
  intros t n m k.
     refine
      (well_founded_ind (Zwf_up_well_founded n)
         (fun k:Z =>
            (forall i:Z, (k <= i <= n)%Z -> (access t i <= m)%Z) ->
            Maximize t n m k) _ _).
     clear k; intros k HR H.
     constructor 1.
       intros; apply H; omega'.
       intros; apply HR.
         unfold Zwf_up; omega'.
         intros; apply H; omega'.
Qed.

(* compatibilitÃ© de  avec  *)
Lemma Maximize_Zle :
 forall (t:array Z) (n m1 m2 k:Z),
   Maximize t n m1 k -> (k <= n)%Z -> (m1 <= m2)%Z -> Maximize t n m2 k.
  Proof.
  intros t n m1 m2 k H0; elim H0.
  intros k0 H1 H2 H3 H4 H5; constructor 1.
  omega'.
 intros; apply H3; omega'.
Qed.

Set Strict Implicit.
Unset Implicit Arguments.
(* ----------- FIN PRELIMINAIRES ----------- *)


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma swap_po_1 : 
  forall (i: Z),
  forall (j: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= i /\ i < (array_length t)) /\ 0 <= j /\ j <
                (array_length t)),
  0 <= i /\ i < (array_length t).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma swap_po_2 : 
  forall (i: Z),
  forall (j: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= i /\ i < (array_length t)) /\ 0 <= j /\ j <
                (array_length t)),
  forall (HW_2: 0 <= i /\ i < (array_length t)),
  forall (result: Z),
  forall (HW_3: result = (access t i)),
  0 <= j /\ j < (array_length t).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma swap_po_3 : 
  forall (i: Z),
  forall (j: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= i /\ i < (array_length t)) /\ 0 <= j /\ j <
                (array_length t)),
  forall (HW_2: 0 <= i /\ i < (array_length t)),
  forall (result: Z),
  forall (HW_3: result = (access t i)),
  forall (HW_4: 0 <= j /\ j < (array_length t)),
  forall (result0: Z),
  forall (HW_5: result0 = (access t j)),
  0 <= i /\ i < (array_length t).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma swap_po_4 : 
  forall (i: Z),
  forall (j: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= i /\ i < (array_length t)) /\ 0 <= j /\ j <
                (array_length t)),
  forall (HW_2: 0 <= i /\ i < (array_length t)),
  forall (result: Z),
  forall (HW_3: result = (access t i)),
  forall (HW_4: 0 <= j /\ j < (array_length t)),
  forall (result0: Z),
  forall (HW_5: result0 = (access t j)),
  forall (HW_6: 0 <= i /\ i < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_7: t0 = (update t i result0)),
  0 <= j /\ j < (array_length t0).
Proof.
intuition.
ArraySubst t0.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma swap_po_5 : 
  forall (i: Z),
  forall (j: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= i /\ i < (array_length t)) /\ 0 <= j /\ j <
                (array_length t)),
  forall (HW_2: 0 <= i /\ i < (array_length t)),
  forall (result: Z),
  forall (HW_3: result = (access t i)),
  forall (HW_4: 0 <= j /\ j < (array_length t)),
  forall (result0: Z),
  forall (HW_5: result0 = (access t j)),
  forall (HW_6: 0 <= i /\ i < (array_length t)),
  forall (t0: (array Z)),
  forall (HW_7: t0 = (update t i result0)),
  forall (HW_8: 0 <= j /\ j < (array_length t0)),
  forall (t1: (array Z)),
  forall (HW_9: t1 = (update t0 j result)),
  (exchange t1 t i j).
Proof.
intuition.
subst; auto with *.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma maximum_po_1 : 
  forall (n: Z),
  forall (k: Z),
  forall (i: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= i) /\ i <= n /\ n < (array_length t) /\
                (Maximize t n (access t i) k)),
  forall (HW_2: k = 0),
  (0 <= i /\ i <= n) /\ (Maximize t n (access t i) 0).
Proof.
intuition.
subst; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma maximum_po_2 : 
  forall (n: Z),
  forall (k: Z),
  forall (i: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= i) /\ i <= n /\ n < (array_length t) /\
                (Maximize t n (access t i) k)),
  forall (HW_3: k <> 0),
  0 <= (k - 1) /\ (k - 1) < (array_length t).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma maximum_po_3 : 
  forall (n: Z),
  forall (k: Z),
  forall (i: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= i) /\ i <= n /\ n < (array_length t) /\
                (Maximize t n (access t i) k)),
  forall (HW_3: k <> 0),
  forall (HW_4: 0 <= (k - 1) /\ (k - 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (k - 1))),
  0 <= i /\ i < (array_length t).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma maximum_po_4 : 
  forall (n: Z),
  forall (k: Z),
  forall (i: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= i) /\ i <= n /\ n < (array_length t) /\
                (Maximize t n (access t i) k)),
  forall (HW_3: k <> 0),
  forall (HW_4: 0 <= (k - 1) /\ (k - 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (k - 1))),
  forall (HW_6: 0 <= i /\ i < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t i)),
  forall (HW_8: result > result0),
  (Zwf 0 (k - 1) k).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma maximum_po_5 : 
  forall (n: Z),
  forall (k: Z),
  forall (i: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= i) /\ i <= n /\ n < (array_length t) /\
                (Maximize t n (access t i) k)),
  forall (HW_3: k <> 0),
  forall (HW_4: 0 <= (k - 1) /\ (k - 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (k - 1))),
  forall (HW_6: 0 <= i /\ i < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t i)),
  forall (HW_8: result > result0),
  forall (HW_9: (Zwf 0 (k - 1) k)),
  (0 <= (k - 1) /\ (k - 1) <= (k - 1)) /\ (k - 1) <= n /\ n <
  (array_length t) /\ (Maximize t n (access t (k - 1)) (k - 1)).
Proof.
intuition; subst.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma maximum_po_6 : 
  forall (n: Z),
  forall (k: Z),
  forall (i: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= i) /\ i <= n /\ n < (array_length t) /\
                (Maximize t n (access t i) k)),
  forall (HW_3: k <> 0),
  forall (HW_4: 0 <= (k - 1) /\ (k - 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (k - 1))),
  forall (HW_6: 0 <= i /\ i < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t i)),
  forall (HW_12: result <= result0),
  (Zwf 0 (k - 1) k).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma maximum_po_7 : 
  forall (n: Z),
  forall (k: Z),
  forall (i: Z),
  forall (t: (array Z)),
  forall (HW_1: (0 <= k /\ k <= i) /\ i <= n /\ n < (array_length t) /\
                (Maximize t n (access t i) k)),
  forall (HW_3: k <> 0),
  forall (HW_4: 0 <= (k - 1) /\ (k - 1) < (array_length t)),
  forall (result: Z),
  forall (HW_5: result = (access t (k - 1))),
  forall (HW_6: 0 <= i /\ i < (array_length t)),
  forall (result0: Z),
  forall (HW_7: result0 = (access t i)),
  forall (HW_12: result <= result0),
  forall (HW_13: (Zwf 0 (k - 1) k)),
  (0 <= (k - 1) /\ (k - 1) <= i) /\ i <= n /\ n < (array_length t) /\
  (Maximize t n (access t i) (k - 1)).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma maxisort_po_1 : 
  forall (t: (array Z)),
  forall (HW_1: 0 <= (array_length t)),
  forall (result: Z),
  forall (HW_2: result = (array_length t)),
  (0 <= (result - 1 + 1) /\ (result - 1 + 1) <= (array_length t)) /\
  (sorted_array t (result - 1 + 1) ((array_length t) - 1)) /\ (permut t t) /\
  (((result - 1 + 1) < (array_length t) ->
    (Maximize t (result - 1) (access t (result - 1 + 1)) 0))).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma maxisort_po_2 : 
  forall (t: (array Z)),
  forall (HW_1: 0 <= (array_length t)),
  forall (result: Z),
  forall (HW_2: result = (array_length t)),
  forall (HW_3: (0 <= (result - 1 + 1) /\ (result - 1 + 1) <=
                (array_length t)) /\
                (sorted_array t (result - 1 + 1) ((array_length t) - 1)) /\
                (permut t t) /\
                (((result - 1 + 1) < (array_length t) ->
                  (Maximize t (result - 1) (access t (result - 1 + 1)) 0)))),
  forall (i: Z),
  forall (t0: (array Z)),
  forall (HW_4: (0 <= (i + 1) /\ (i + 1) <= (array_length t0)) /\
                (sorted_array t0 (i + 1) ((array_length t0) - 1)) /\
                (permut t0 t) /\
                (((i + 1) < (array_length t0) ->
                  (Maximize t0 i (access t0 (i + 1)) 0)))),
  forall (HW_5: i >= 0),
  (0 <= i /\ i <= i) /\ i <= i /\ i < (array_length t0) /\
  (Maximize t0 i (access t0 i) i).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma maxisort_po_3 : 
  forall (t: (array Z)),
  forall (HW_1: 0 <= (array_length t)),
  forall (result: Z),
  forall (HW_2: result = (array_length t)),
  forall (HW_3: (0 <= (result - 1 + 1) /\ (result - 1 + 1) <=
                (array_length t)) /\
                (sorted_array t (result - 1 + 1) ((array_length t) - 1)) /\
                (permut t t) /\
                (((result - 1 + 1) < (array_length t) ->
                  (Maximize t (result - 1) (access t (result - 1 + 1)) 0)))),
  forall (i: Z),
  forall (t0: (array Z)),
  forall (HW_4: (0 <= (i + 1) /\ (i + 1) <= (array_length t0)) /\
                (sorted_array t0 (i + 1) ((array_length t0) - 1)) /\
                (permut t0 t) /\
                (((i + 1) < (array_length t0) ->
                  (Maximize t0 i (access t0 (i + 1)) 0)))),
  forall (HW_5: i >= 0),
  forall (HW_6: (0 <= i /\ i <= i) /\ i <= i /\ i < (array_length t0) /\
                (Maximize t0 i (access t0 i) i)),
  forall (result0: Z),
  forall (HW_7: (0 <= result0 /\ result0 <= i) /\
                (Maximize t0 i (access t0 result0) 0)),
  (0 <= i /\ i < (array_length t0)) /\ 0 <= result0 /\ result0 <
  (array_length t0).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma maxisort_po_4 : 
  forall (t: (array Z)),
  forall (HW_1: 0 <= (array_length t)),
  forall (result: Z),
  forall (HW_2: result = (array_length t)),
  forall (HW_3: (0 <= (result - 1 + 1) /\ (result - 1 + 1) <=
                (array_length t)) /\
                (sorted_array t (result - 1 + 1) ((array_length t) - 1)) /\
                (permut t t) /\
                (((result - 1 + 1) < (array_length t) ->
                  (Maximize t (result - 1) (access t (result - 1 + 1)) 0)))),
  forall (i: Z),
  forall (t0: (array Z)),
  forall (HW_4: (0 <= (i + 1) /\ (i + 1) <= (array_length t0)) /\
                (sorted_array t0 (i + 1) ((array_length t0) - 1)) /\
                (permut t0 t) /\
                (((i + 1) < (array_length t0) ->
                  (Maximize t0 i (access t0 (i + 1)) 0)))),
  forall (HW_5: i >= 0),
  forall (HW_6: (0 <= i /\ i <= i) /\ i <= i /\ i < (array_length t0) /\
                (Maximize t0 i (access t0 i) i)),
  forall (result0: Z),
  forall (HW_7: (0 <= result0 /\ result0 <= i) /\
                (Maximize t0 i (access t0 result0) 0)),
  forall (HW_8: (0 <= i /\ i < (array_length t0)) /\ 0 <= result0 /\
                result0 < (array_length t0)),
  forall (t1: (array Z)),
  forall (HW_9: (exchange t1 t0 i result0)),
  forall (i0: Z),
  forall (HW_10: i0 = (i - 1)),
  ((0 <= (i0 + 1) /\ (i0 + 1) <= (array_length t1)) /\
  (sorted_array t1 (i0 + 1) ((array_length t1) - 1)) /\ (permut t1 t) /\
  (((i0 + 1) < (array_length t1) -> (Maximize t1 i0 (access t1 (i0 + 1)) 0)))) /\
  (Zwf 0 (i0 + 1) (i + 1)).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma maxisort_po_5 : 
  forall (t: (array Z)),
  forall (HW_1: 0 <= (array_length t)),
  forall (result: Z),
  forall (HW_2: result = (array_length t)),
  forall (HW_3: (0 <= (result - 1 + 1) /\ (result - 1 + 1) <=
                (array_length t)) /\
                (sorted_array t (result - 1 + 1) ((array_length t) - 1)) /\
                (permut t t) /\
                (((result - 1 + 1) < (array_length t) ->
                  (Maximize t (result - 1) (access t (result - 1 + 1)) 0)))),
  forall (i: Z),
  forall (t0: (array Z)),
  forall (HW_4: (0 <= (i + 1) /\ (i + 1) <= (array_length t0)) /\
                (sorted_array t0 (i + 1) ((array_length t0) - 1)) /\
                (permut t0 t) /\
                (((i + 1) < (array_length t0) ->
                  (Maximize t0 i (access t0 (i + 1)) 0)))),
  forall (HW_11: i < 0),
  (sorted_array t0 0 ((array_length t0) - 1)) /\ (permut t0 t).
Proof.
intuition.
Save.

(* DÃ©but: preuve de  *)

  Proof.
  intros; split.
  Omega'.
  rewrite Test4 in Pre18; tauto.
Qed.

   Proof.
   intros; Omega'.
Qed.

  Proof.
  intros; Omega'.
Qed.

Proof.
repeat (split; [ Omega' | auto ]).
subst nk.
ring (k0 - 1 + 1)%Z; intros;
 apply Maximize_Zle with (m1 := access t i0); Omega' || tauto.
Qed.

  Proof.
  intros; subst nk; unfold Zwf; Omega'.
  Qed.

  Proof.
  intros; subst nk.
  repeat (split; [ Omega' | auto ]); ring (k0 - 1 + 1)%Z; tauto.
Qed.

  Proof.
  intros; subst nk.
  unfold Zwf; Omega'.
  Qed.


(* fin preuve de maximum *)

  Proof.
  intros; split.
 Omega'.
 split.
 Omega'.
 split.
 Omega'.
  constructor 1.
 Omega'.
  intros H; absurd (i1 < i1)%Z; Omega'.
Qed.

  Proof.
  intros; Omega'.
Qed.

 Proof.
 intros; decompose [and] Pre8; clear Pre8; split.
   ArrayLength.
   split.
   omega.
   split.
   (* post-condition 1 *)
   unfold sorted_array in H0; unfold sorted_array.
   intros C1 k C2 C3; case Post9.
    intros Clength C4 C5 C6 C7 C8.
     case (Z_eq_dec k i1).
       intros C9; rewrite C9; rewrite C6; rewrite C8; try Omega'.
       apply Maximize_ext1 with (n := i1) (k := 0%Z); try Omega'.
         apply H5; Omega'.
       intros C9; rewrite C8; try Omega'.
 rewrite C8; try Omega'.
       apply H0; try Omega'.
   (* post-condition 2 *)
   split.
 apply permut_trans with (t' := t0); auto.
   eapply exchange_is_permut; eauto.
   (* post-condition 3 *)
   decompose [and] Post7; clear Post7.
 case Post9; clear Post9.
   intros Clength C1 C2 C3 C4 C5 C5a; replace (i0 + 1)%Z with i1.
 rewrite C3.
     apply Maximize_ext2; intros i' C6.
     case (Z_eq_dec i' r).
       intros C7; rewrite C7; rewrite C4.
         apply Maximize_ext1 with (n := i1) (k := 0%Z); try Omega';
          auto.
       intros; rewrite C5; try Omega'.
         apply Maximize_ext1 with (n := i1) (k := 0%Z); try Omega';
          auto.
   omega.
   unfold Zwf; omega.
Qed.

  Proof.
  intros; subst i; ring (array_length t - 1 + 1)%Z; split.
   Omega'.
  split.
 unfold sorted_array; intros H;
  absurd (array_length t <= array_length t - 1)%Z; [ Omega' | auto ].
  split.
 apply permut_refl.
  intros H; absurd (array_length t < array_length t)%Z;
   [ Omega' | auto ].
Qed.

  Proof.
  intros; cut ((i1 + 1)%Z = 0%Z);
   [ intros H; rewrite H in Post2; split; tauto | Omega' ].
Qed.


