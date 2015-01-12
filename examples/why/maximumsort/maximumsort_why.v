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


Proof.
intuition.
Save.

Proof.
intuition.
Save.

Proof.
intuition.
Save.

Proof.
intuition.
ArraySubst t0.
Save.

Proof.
intuition.
subst; auto with *.
Save.


(*Why type*) Definition farray: Set ->Set.
Admitted.

(*Why logic*) Definition access : forall (A1:Set), (array A1) -> Z -> A1.
Admitted.
Implicit Arguments access.

(*Why logic*) Definition update :
  forall (A1:Set), (array A1) -> Z -> A1 -> (array A1).
Admitted.
Implicit Arguments update.

(*Why axiom*) Lemma access_update :
  forall (A1:Set),
  (forall (a:(array A1)),
   (forall (i:Z), (forall (v:A1), (access (update a i v) i) = v))).
Admitted.

(*Why axiom*) Lemma access_update_neq :
  forall (A1:Set),
  (forall (a:(array A1)),
   (forall (i:Z),
    (forall (j:Z),
     (forall (v:A1), (i <> j -> (access (update a i v) j) = (access a j)))))).
Admitted.

(*Why logic*) Definition array_length : forall (A1:Set), (array A1) -> Z.
Admitted.
Implicit Arguments array_length.

(*Why predicate*) Definition sorted_array  (t:(array Z)) (i:Z) (j:Z)
  := (forall (k1:Z),
      (forall (k2:Z),
       ((i <= k1 /\ k1 <= k2) /\ k2 <= j -> (access t k1) <= (access t k2)))).

(*Why predicate*) Definition exchange (A111:Set) (a1:(array A111)) (a2:(array A111)) (i:Z) (j:Z)
  := (array_length a1) = (array_length a2) /\
     (access a1 i) = (access a2 j) /\ (access a2 i) = (access a1 j) /\
     (forall (k:Z), (k <> i /\ k <> j -> (access a1 k) = (access a2 k))).
Implicit Arguments exchange.

(*Why logic*) Definition permut :
  forall (A1:Set), (array A1) -> (array A1) -> Z -> Z -> Prop.
Admitted.
Implicit Arguments permut.

(*Why axiom*) Lemma permut_refl :
  forall (A1:Set),
  (forall (t:(array A1)), (forall (l:Z), (forall (u:Z), (permut t t l u)))).
Admitted.

(*Why axiom*) Lemma permut_sym :
  forall (A1:Set),
  (forall (t1:(array A1)),
   (forall (t2:(array A1)),
    (forall (l:Z), (forall (u:Z), ((permut t1 t2 l u) -> (permut t2 t1 l u)))))).
Admitted.

(*Why axiom*) Lemma permut_trans :
  forall (A1:Set),
  (forall (t1:(array A1)),
   (forall (t2:(array A1)),
    (forall (t3:(array A1)),
     (forall (l:Z),
      (forall (u:Z),
       ((permut t1 t2 l u) -> ((permut t2 t3 l u) -> (permut t1 t3 l u)))))))).
Admitted.

(*Why axiom*) Lemma permut_exchange :
  forall (A1:Set),
  (forall (a1:(array A1)),
   (forall (a2:(array A1)),
    (forall (l:Z),
     (forall (u:Z),
      (forall (i:Z),
       (forall (j:Z),
        (l <= i /\ i <= u ->
         (l <= j /\ j <= u -> ((exchange a1 a2 i j) -> (permut a1 a2 l u)))))))))).
Admitted.

(*Why axiom*) Lemma exchange_upd :
  forall (A1:Set),
  (forall (a:(array A1)),
   (forall (i:Z),
    (forall (j:Z),
     (exchange a (update (update a i (access a j)) j (access a i)) i j)))).
Admitted.

(*Why axiom*) Lemma permut_weakening :
  forall (A1:Set),
  (forall (a1:(array A1)),
   (forall (a2:(array A1)),
    (forall (l1:Z),
     (forall (r1:Z),
      (forall (l2:Z),
       (forall (r2:Z),
        ((l1 <= l2 /\ l2 <= r2) /\ r2 <= r1 ->
         ((permut a1 a2 l2 r2) -> (permut a1 a2 l1 r1))))))))).
Admitted.

(*Why axiom*) Lemma permut_eq :
  forall (A1:Set),
  (forall (a1:(array A1)),
   (forall (a2:(array A1)),
    (forall (l:Z),
     (forall (u:Z),
      (l <= u ->
       ((permut a1 a2 l u) ->
        (forall (i:Z), (i < l \/ u < i -> (access a2 i) = (access a1 i))))))))).
Admitted.

(*Why predicate*) Definition permutation (A120:Set) (a1:(array A120)) (a2:(array A120))
  := (permut a1 a2 0 ((array_length a1) - 1)).
Implicit Arguments permutation.

(*Why axiom*) Lemma array_length_update :
  forall (A1:Set),
  (forall (a:(array A1)),
   (forall (i:Z),
    (forall (v:A1), (array_length (update a i v)) = (array_length a)))).
Admitted.

(*Why axiom*) Lemma permut_array_length :
  forall (A1:Set),
  (forall (a1:(array A1)),
   (forall (a2:(array A1)),
    (forall (l:Z),
     (forall (u:Z),
      ((permut a1 a2 l u) -> (array_length a1) = (array_length a2)))))).
Admitted.

(*Why predicate*) Definition Maximize  (t:(array Z)) (n:Z) (x:Z) (k:Z)
  := (forall (i:Z), (k <= i /\ i <= n -> (access t k) <= x)).

Proof.
intuition.
subst; auto.
Save.

Proof.
intuition.
Save.

Proof.
intuition.
Save.

Proof.
intuition.
Save.

Proof.
intuition; subst.
Save.

Proof.
intuition.
Save.

Proof.
intuition.
Save.


Proof.
intuition.
Save.

Proof.
intuition.
Save.

Proof.
intuition.
Save.

Proof.
intuition.
Save.

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



Proof.
(* FILL PROOF HERE *)
Save.
