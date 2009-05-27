
Require Import Why.
Require Import ZArith.
Require Import Zcomplements.
Require Import Omega.
 
Ltac Omega' := abstract omega.

(* Parameters and axioms *)

Parameter v : Z.

(* Specification *)

Inductive In (t:array Z) (l u:Z) : Prop :=
    In_cons : forall i:Z, (l <= i <= u)%Z -> access t i = v -> In t l u.

Definition mean (x y:Z) := Zdiv2 (x + y).

(* Lemmas *)

Lemma le_mean : forall x y:Z, (0 <= x <= y)%Z -> (x <= mean x y)%Z.
Proof.
intros.
apply Zmult_le_reg_r with (p := 2%Z).
omega.
rewrite Zmult_comm.
rewrite (Zmult_comm (mean x y) 2).
unfold mean.
elim (Zeven_odd_dec (x + y)); intro.
rewrite <- Zeven_div2 with (x + y)%Z.
omega.
assumption.
elim (Z_eq_dec x y); intro.
absurd (x = y); try assumption.
rewrite a in b.
absurd (Zodd (y + y)); try assumption.
absurd ((y + y)%Z = (2 * Zdiv2 (y + y) + 1)%Z).
omega.
apply Zodd_div2.
omega.
assumption.
cut ((x + y)%Z = (2 * Zdiv2 (x + y) + 1)%Z).
omega.
apply Zodd_div2.
omega.
assumption.
Qed.

Lemma ge_mean : forall x y:Z, (0 <= x <= y)%Z -> (mean x y <= y)%Z.
Proof.
intros.
apply Zmult_le_reg_r with (p := 2%Z).
omega.
rewrite Zmult_comm.
rewrite (Zmult_comm y 2).
unfold mean.
elim (Zeven_odd_dec (x + y)); intro.
rewrite <- Zeven_div2 with (x + y)%Z.
omega.
assumption.
cut ((x + y)%Z = (2 * Zdiv2 (x + y) + 1)%Z).
omega.
apply Zodd_div2.
omega.
assumption.
Qed.

Lemma In_right_side :
 forall t:array Z,
   sorted_array t 1 (array_length t - 1) ->
   forall l u:Z,
     (1 <= l)%Z ->
     (u <= array_length t - 1)%Z ->
     (l <= u)%Z ->
     (l <= mean l u <= u)%Z ->
     (In t 1 (array_length t - 1) -> In t l u) ->
     (access t (mean l u) < v)%Z ->
     In t 1 (array_length t - 1) -> In t (mean l u + 1) u.
     Proof.
     intros t Hsorted l u Hl Hu Hlu Hm Inv Hv H.
generalize (Inv H).
 intro.
decompose [In] H0.
apply In_cons with i.
elim (Z_gt_le_dec (mean l u + 1) i); intro.
absurd (access t i = v).
apply Zlt_not_eq.
apply Zle_lt_trans with (access t (mean l u)).
apply sorted_elements with (n := 1%Z) (m := (array_length t - 1)%Z).
assumption.
Omega'.
Omega'.
Omega'.
Omega'.
assumption.
assumption.
Omega'.
assumption.
Qed.

Lemma In_left_side :
 forall t:array Z,
   sorted_array t 1 (array_length t - 1) ->
   forall l u:Z,
     (1 <= l)%Z ->
     (u <= array_length t - 1)%Z ->
     (l <= u)%Z ->
     (l <= mean l u <= u)%Z ->
     (In t 1 (array_length t - 1) -> In t l u) ->
     (access t (mean l u) > v)%Z ->
     In t 1 (array_length t - 1) -> In t l (mean l u - 1).
     Proof.
     intros t Hsorted l u Hl Hu Hlu Hm Inv Hv H.
generalize (Inv H).
 intro.
decompose [In] H0.
apply In_cons with i.
elim (Z_gt_le_dec i (mean l u - 1)); intro.
absurd (access t i = v).
apply sym_not_eq.
apply Zlt_not_eq.
apply Zlt_le_trans with (access t (mean l u)).
Omega'.
apply sorted_elements with (n := 1%Z) (m := (array_length t - 1)%Z).
assumption.
Omega'.
Omega'.
Omega'.
Omega'.
assumption.
Omega'.
assumption.
Qed.

(* Obligations *)

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

(*Why predicate*) Definition exchange (A102:Set) (a1:(array A102)) (a2:(array A102)) (i:Z) (j:Z)
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

(*Why predicate*) Definition permutation (A111:Set) (a1:(array A111)) (a2:(array A111))
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

(*Why logic*) Definition v : Z.
Admitted.

(*Why function*) Definition mean  (x:Z) (y:Z) := ((Zdiv (x + y) 2)).

(*Why axiom*) Lemma mean :
  (forall (x:Z),
   (forall (y:Z), (x <= y -> x <= (mean x y) /\ (mean x y) <= y))).
Admitted.

(*Why predicate*) Definition In  (t:(array Z)) (l:Z) (u:Z)
  := (exists i:Z, (l <= i /\ i <= u) /\ (access t i) = v).

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition; subst.
apply le_mean; intuition.
apply ge_mean; intuition.
Save.

Proof.
intuition.
Save.

Proof.
intuition.
subst; apply In_right_side; intuition.
Save.

Proof.
intuition.
subst; apply In_left_side; intuition.
Save.

Proof.
intuition; subst.
absurd (mean l0 u0 = 0); omega.
omega.
Save.

Proof.
intuition; subst.
assert (1 <= p0 \/ p0=0). omega. intuition.
subst; right; intuition.
assert (h: (In t l0 u0)). assumption.
inversion h; omega.
Save.


Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.



