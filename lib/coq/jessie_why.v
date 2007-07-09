Ltac caseeq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Why.

Set Implicit Arguments.

Require Import Map. (* dans Map.v (temporairement) *)

(*Why type*) Definition alloc_table: Set ->Set.
exact (fun _ => Map Z).
Defined.

(*Why type*) Definition pointer: Set ->Set.
exact (fun _ => prod ad Z).
Defined.

Lemma N_eq_diff: forall (a b: N), a = b \/ a <> b.
Proof.
intros.
assert (E: (b ?= b)%N = Eq).
apply Ncompare_refl.
caseeq (a ?= b)%N; intro H; [left | right | right].
apply Ncompare_Eq_eq; auto.
intro; subst.
rewrite H in E.
inversion E.
intro; subst.
rewrite H in E.
inversion E.
Qed.

Lemma Z_eq_diff: forall (a b: Z), a = b \/ a <> b.
Proof.
intros.
assert (E: (b ?= b) = Eq).
apply Zcompare_refl.
caseeq (a ?= b); intro H; [left | right | right].
apply Zcompare_Eq_eq; auto.
intro; subst.
rewrite H in E.
inversion E.
intro; subst.
rewrite H in E.
inversion E.
Qed.

Lemma eq_pointer (A: Set): forall (p q: pointer A), p = q \/ p <> q.
Proof.
intros.
unfold pointer in *.
unfold ad in *.
induction p as [p1 p2].
induction q as [q1 q2].
assert (H1: p1 = q1 \/ p1 <> q1).
apply N_eq_diff.
assert (H2: p2 = q2 \/ p2 <> q2).
apply Z_eq_diff.
destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2]; subst.
left; auto.
right.
intro H3.
assert (H4: snd (q1, p2) = snd (q1, q2)).
rewrite H3; auto.
simpl in H4.
auto.
right.
intro H3.
assert (H4: fst (p1, q2) = fst (q1, q2)).
rewrite H3; auto.
simpl in H4.
auto.
right.
intro H3.
assert (H4: fst (p1, p2) = fst (q1, q2)).
rewrite H3; auto.
simpl in H4.
auto.
Qed.

Definition block_length (A: Set) (a: alloc_table A) (p: pointer A) :=
  match fst p with
    0%N => 0
  | _ =>
  match MapGet Z a (fst p) with
    None => 0
  | Some size => size
  end
  end.

(*Why logic*) Definition offset_max :
  forall (A1:Set), (alloc_table A1) -> (pointer A1) -> Z.
exact (fun A1 a p => block_length a p - snd p - 1).
Defined.

(*Why logic*) Definition offset_min :
  forall (A1:Set), (alloc_table A1) -> (pointer A1) -> Z.
exact (fun A1 t p => -snd p).
Defined.

(*Why predicate*) Definition valid (A226:Set) (a:(alloc_table A226))
  (p:(pointer A226)) := (offset_min a p) <= 0 /\ (offset_max a p) >= 0.

(*Why logic*) Definition shift :
  forall (A1:Set), (pointer A1) -> Z -> (pointer A1).
exact (fun A1 p i => (fst p, snd p + i)).
Defined.
Implicit Arguments shift.

(*Why axiom*) Lemma offset_max_shift :
  forall (A1:Set),
  (forall (a:(alloc_table A1)),
   (forall (p:(pointer A1)),
    (forall (i:Z), (offset_max a (shift p i)) = ((offset_max a p) - i)))).
Proof.
intros A1 a p i.
unfold shift.
unfold offset_max.
unfold block_length.
simpl.
case (fst p); intuition.
Defined.
Implicit Arguments offset_max_shift.

(*Why axiom*) Lemma offset_min_shift :
  forall (A1:Set),
  (forall (a:(alloc_table A1)),
   (forall (p:(pointer A1)),
    (forall (i:Z), (offset_min a (shift p i)) = ((offset_min a p) - i)))).
Proof.
intros A1 a p i.
unfold shift.
unfold offset_min.
simpl.
intuition.
Defined.
Implicit Arguments offset_min_shift.

Lemma not_found_not_valid (A: Set) (a: alloc_table A) (p: pointer A):
  MapGet Z a (fst p) = None -> ~valid a p.
Proof with intuition.
intros A a p H V.
unfold valid in V.
unfold offset_min in V.
unfold offset_max in V.
assert (block_length a p = 0) as BLZ.
unfold block_length.
rewrite H...
case (fst p)...
rewrite BLZ in V...
Defined.

(* Une mémoire est une paire constituée de son contenu et
d'une valeur par défaut, qui nous servira pour select. Son
contenu est lui-même une paire de deux maps, la première pour
les indices positifs ou nuls (valides), l'autre pour les indices
négatifs (donc invalides mais c'est plus simple pour les lemmes après). *)
Definition block (T: Set) := prod (Map T) (Map T).
Definition blocks (T: Set) := Map (block T).

(*Why logic*) Definition null : forall (A1:Set), (pointer A1).
exact (fun _ => (0%N, 0%Z)).
Defined.
Set Contextual Implicit.
Implicit Arguments null.
Unset Contextual Implicit.

(*Why axiom*) Lemma null_not_valid :
  forall (A1:Set), (forall (a:(alloc_table A1)), ~(valid a (@null A1))).
Proof.
intros.
unfold null.
unfold valid.
intuition.
Defined.

(*Why type*) Definition memory: Set -> Set ->Set.
exact (fun S T => prod (blocks T) T).
Defined.

Definition mem_blocks := fst.
Definition mem_def := snd.
Definition block_pos := fst.
Definition block_neg := snd.
Definition empty_block (T: Set) := pair (newMap T) (newMap T).
Definition make_mem (S T: Set) (blocks: blocks T) (def: T): memory S T :=
  pair blocks def.
Definition make_block (T: Set) (pos: Map T) (neg: Map T): block T :=
  pair pos neg.

Definition option_value (A: Set) (def: A) (O: option A): A :=
  match O with
    None => def
  | Some a => a
  end.

Definition mem_get_block (S T: Set) (m: memory S T) (a: ad) :=
  match MapGet (block T) (mem_blocks m) a with
    None => empty_block T
  | Some block => block
  end.

Definition block_get_item (T: Set) (b: block T) (def: T) (i: Z) :=
  match i with
    Z0 => option_value def (MapGet T (block_pos b) N0)
  | Zpos p => option_value def (MapGet T (block_pos b) (Npos p))
  | Zneg p => option_value def (MapGet T (block_neg b) (Npos p))
  end.

Definition mem_get_item (S T: Set) (m: memory S T) (a: ad) (i: Z) :=
  block_get_item (mem_get_block m a) (snd m) i.

(*Why logic*) Definition select :
  forall (A1:Set), forall (A2:Set), (memory A2 A1) -> (pointer A2) -> A1.
exact (fun T S m p => mem_get_item m (fst p) (snd p)).
Defined.

Definition block_set_item (T: Set) (b: block T) (i: Z) (item: T): block T :=
  match i with
    Z0 =>
      make_block (MapPut T (block_pos b) N0 item) (block_neg b)
  | Zpos p =>
      make_block (MapPut T (block_pos b) (Npos p) item) (block_neg b)
  | Zneg p =>
      make_block (block_pos b) (MapPut T (block_neg b) (Npos p) item)
  end.

Definition mem_set_block (S T: Set) (m: memory S T) (a: ad) (b: block T) :=
  make_mem S (MapPut (block T) (mem_blocks m) a b) (mem_def m).

Definition mem_set_item (S T: Set) (m: memory S T) (a: ad) (i: Z) (item: T) :=
  mem_set_block m a (block_set_item (mem_get_block m a) i item).

(*Why logic*) Definition store :
  forall (A1:Set), forall (A2:Set), (memory A1 A2) -> (pointer A1)
  -> A2 -> (memory A1 A2).
exact (fun S T m p item => mem_set_item m (fst p) (snd p) item).
Defined.

Lemma map_get_put_eq (T: Set): forall m a i,
  MapGet T (MapPut T m a i) a = Some i.
Proof.
intros T m a i.
generalize (MapPut_semantics T m a i); intro map_eq.
unfold eqm in map_eq.
assert (MapGet T (MapPut T m a i) a =
  (if Ndec.Neqb a a then Some i else MapGet T m a)) as map_eq_a.
apply map_eq.
clear map_eq.
assert (Ndec.Neqb a a = true) as aa.
apply Ndec.Neqb_correct.
rewrite aa in map_eq_a; auto.
Qed.

Lemma mem_block_get_set_eq (S T: Set): forall m a b,
  @mem_get_block S T (@mem_set_block S T m a b) a = b.
Proof.
intros S T m a b.
unfold mem_set_block.
unfold mem_get_block.
simpl.
generalize (map_get_put_eq (mem_blocks m) a b); intro H.
rewrite H; auto.
Qed.

Lemma block_get_set_eq (T: Set): forall def b i x,
  @block_get_item T (block_set_item b i x) def i = x.
Proof.
intros T def b i x.
unfold block_get_item.
unfold block_set_item.
unfold block_pos.
unfold make_block.
unfold block_neg.
case i; try intro p; simpl.
generalize (map_get_put_eq (fst b) 0%N x); intro H; rewrite H; auto.
generalize (map_get_put_eq (fst b) (Npos p) x); intro H; rewrite H; auto.
generalize (map_get_put_eq (snd b) (Npos p) x); intro H; rewrite H; auto.
Qed.

Lemma mem_get_set_eq (S T: Set): forall m a i x,
  @mem_get_item S T (@mem_set_item S T m a i x) a i = x.
Proof.
intros S T mem a i x.
set (new_mem := mem_set_item mem a i x).
unfold mem_get_item.
set (def := snd mem).
assert (def = snd mem) as def_eq1; auto.
assert (def = snd new_mem) as def_eq2; auto.
rewrite <- def_eq2.
unfold new_mem.
unfold mem_set_item.
generalize (mem_block_get_set_eq mem a
  (block_set_item (mem_get_block mem a) i x)); intro H; rewrite H; clear H.
apply block_get_set_eq.
Qed.

(*Why axiom*) Lemma select_store_eq :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(memory A1 A2)),
   (forall (p1:(pointer A1)),
    (forall (p2:(pointer A1)),
     (forall (a:A2), (p1 = p2 -> (select (store m p1 a) p2) = a))))).
Proof.
intros S T m p q x peq.
rewrite <- peq.
clear q peq.
unfold select.
unfold store.
apply mem_get_set_eq.
Qed.

Lemma Ndiff: forall a b, a <> b -> Ndec.Neqb a b = false.
Proof.
intros a b diff.
caseeq (Ndec.Neqb a b); intro H; auto.
assert (a = b) as H'.
apply (Ndec.Neqb_complete a b); auto.
assert False as F.
apply diff; auto.
destruct F.
Qed.

Lemma Ndiff': forall a b, Ndec.Neqb a b = false -> a <> b.
Proof.
intros a b neq eq.
generalize (Ndec.Neqb_correct a).
intro H.
rewrite <- eq in neq.
assert (false = true).
rewrite <- neq.
rewrite <- H.
trivial.
discriminate H0.
Qed.

Lemma map_get_put_diff (T: Set): forall m a b i,
  a <> b -> MapGet T (MapPut T m a i) b = MapGet T m b.
Proof.
intros T m a b i diff.
generalize (MapPut_semantics T m a i); intro map_eq.
unfold eqm in map_eq.
assert (MapGet T (MapPut T m a i) b =
  (if Ndec.Neqb a b then Some i else MapGet T m b)) as map_eq_b.
apply map_eq.
clear map_eq.
assert (Ndec.Neqb a b = false) as aa.
apply Ndiff; auto.
rewrite aa in map_eq_b.
auto.
Qed.

Lemma mem_block_get_set_diff (S T: Set): forall m a1 a2 b, a1 <> a2 ->
  @mem_get_block S T (@mem_set_block S T m a1 b) a2
    = @mem_get_block S T m a2.
Proof.
intros S T m a1 a2 b.
unfold mem_set_block.
unfold mem_get_block.
simpl.
intro diff.
generalize (@map_get_put_diff (block T) (mem_blocks m) a1 a2 b); intro H.
rewrite (H diff); auto.
Qed.

Lemma Npos_inv: forall p q, p <> q -> Npos p <> Npos q.
Proof.
intros p q diff diff'.
inversion diff' as [eq].
apply diff.
apply eq.
Qed.

Lemma block_get_set_diff (T: Set): forall def b i j x, i <> j ->
  @block_get_item T (block_set_item b i x) def j
    = @block_get_item T b def j.
Proof.
intros T def b i j x diff.
unfold block_get_item.
unfold block_set_item.
unfold block_pos.
unfold block_neg.
unfold make_block.
caseeq j.
intro jval.
caseeq i.
intro ival.
assert False; intuition.
intros p ival; simpl.
generalize (@map_get_put_diff T (fst b) (Npos p) 0%N x);
  intro H; rewrite H; auto.
discriminate.
auto.
intros p jval.
caseeq i.
intro ival; simpl.
generalize (@map_get_put_diff T (fst b) 0%N (Npos p) x);
  intro H; rewrite H; auto.
discriminate.
intros q ival; simpl.
generalize (@map_get_put_diff T (fst b) (Npos q) (Npos p) x);
  intro H; rewrite H; auto.
apply Npos_inv; intro pqeq; rewrite pqeq in ival; intuition.
auto.
intros p jval.
caseeq i.
auto.
auto.
intros q ival; simpl.
generalize (@map_get_put_diff T (snd b) (Npos q) (Npos p) x);
  intro H; rewrite H; auto.
apply Npos_inv; intro pqeq; rewrite pqeq in ival; intuition.
Qed.

Lemma mem_get_set_diff (S T: Set): forall m a a' i i' x, a <> a' \/ i <> i' ->
  @mem_get_item S T (@mem_set_item S T m a i x) a' i'
    = @mem_get_item S T m a' i'.
Proof.
intros S T mem a a' i i' x diff.
set (new_mem := mem_set_item mem a i x).
unfold mem_get_item.
set (def := snd mem).
assert (def = snd mem) as def_eq1; auto.
assert (def = snd new_mem) as def_eq2; auto.
rewrite <- def_eq2.
unfold new_mem.
unfold mem_set_item.
assert (a <> a' \/ a = a' /\ i <> i') as diff'.
caseeq (Ndec.Neqb a a'); intro H.
assert (a = a') as H'.
apply Ndec.Neqb_complete; auto.
right; intuition.
left.
apply Ndiff'; trivial.
clear diff.
destruct diff' as [diff | diff].
generalize (@mem_block_get_set_diff S T mem a a'
  (block_set_item (mem_get_block mem a) i x));
  intro H; rewrite H; auto.
destruct diff as [aa ii].
rewrite <- aa.
generalize (@mem_block_get_set_eq S T mem a
  (block_set_item (mem_get_block mem a) i x));
  intro H; rewrite H.
apply block_get_set_diff; trivial.
Qed.

Lemma Neq_or_diff: forall (p q: N), p = q \/ p <> q.
Proof.
intros p q.
assert (if Ndec.Neqb p q then p = q \/ p <> q else p = q \/ p <> q).
caseeq (Ndec.Neqb p q); intro H.
left; apply Ndec.Neqb_complete; trivial.
right; apply Ndiff'; trivial.
caseeq (Ndec.Neqb p q); intro H'; rewrite H' in H; trivial.
Qed.

Lemma pointer_eq (S: Set): forall (p q: pointer S),
  p = q <-> fst p = fst q /\ snd p = snd q.
Proof.
intros S p q.
split; intro H.
split; rewrite H; auto.
destruct H as [H1 H2].
apply (injective_projections p q); auto.
Qed.

Lemma pointer_diff (S: Set): forall (p q: pointer S),
  p <> q <-> fst p <> fst q \/ snd p <> snd q.
Proof.
intros S p q.
split; intro H.
generalize (Neq_or_diff (fst p) (fst q)); intro H'.
destruct H' as [Heq | Hdiff]; auto.
right.
intro Sdiff.
apply H.
apply (injective_projections p q); auto.
intro eq.
rewrite eq in H.
destruct H; apply H; trivial.
Qed.

(*Why axiom*) Lemma select_store_neq :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(memory A1 A2)),
   (forall (p1:(pointer A1)),
    (forall (p2:(pointer A1)),
     (forall (a:A2),
      (~(p1 = p2) -> (select (store m p1 a) p2) = (select m p2)))))).
Proof.
intros S T m p q x.
unfold select.
unfold store.
intro diff.
apply mem_get_set_diff.
setoid_rewrite <- (pointer_diff p q); auto.
Qed.

(*Why type*) Definition pset: Set ->Set.
Admitted.


(*Why logic*) Definition pset_empty : forall (A1:Set), (pset A1).
Admitted.


(*Why logic*) Definition pset_singleton :
  forall (A1:Set), (pointer A1) -> (pset A1).
Admitted.

(*Why logic*) Definition pset_deref :
  forall (A1:Set), forall (A2:Set), (memory A2 (pointer A1))
  -> (pset A2) -> (pset A1).
Admitted.
Implicit Arguments pset_deref.

(*Why logic*) Definition pset_union :
  forall (A1:Set), (pset A1) -> (pset A1) -> (pset A1).
Admitted.

(*Why logic*) Definition pset_range :
  forall (A1:Set), (pset A1) -> Z -> Z -> (pset A1).
Admitted.
Implicit Arguments pset_range.

(*Why logic*) Definition in_pset :
  forall (A1:Set), (pointer A1) -> (pset A1) -> Prop.
Admitted.

(*Why axiom*) Lemma in_pset_empty :
  forall (A1:Set), (forall (p:(pointer A1)), ~(in_pset p (@pset_empty A1))).
Admitted.

(*Why axiom*) Lemma in_pset_singleton :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)), ((in_pset p (pset_singleton q)) <-> p = q))).
Admitted.

(*Why axiom*) Lemma in_pset_deref :
  forall (A1:Set), forall (A2:Set),
  (forall (p:(pointer A1)),
   (forall (m:(memory A2 (pointer A1))),
    (forall (q:(pset A2)),
     ((in_pset p (pset_deref m q)) <->
      (exists r:(pointer A2), (in_pset r q) /\ p = (select m r)))))).
Admitted.
Implicit Arguments in_pset_deref.

(*Why axiom*) Lemma in_pset_range :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pset A1)),
    (forall (a:Z),
     (forall (b:Z),
      ((in_pset p (pset_range q a b)) <->
       (exists i:Z,
        (exists r:(pointer A1), a <= i /\ i <= b /\ (in_pset r q) /\
         p = (shift r i)))))))).
Admitted.
Implicit Arguments in_pset_range.

(*Why axiom*) Lemma in_pset_union :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (s1:(pset A1)),
    (forall (s2:(pset A1)),
     ((in_pset p (pset_union s1 s2)) <-> (in_pset p s1) \/ (in_pset p s2))))).
Admitted.


(*Why predicate*) Definition not_assigns (A254:Set)
  (A253:Set) (a:(alloc_table A253)) (m1:(memory A253 A254)) (m2:(memory A253
  A254)) (l:(pset A253))
  := (forall (p:(pointer A253)),
      ((valid a p) /\ ~(in_pset p l) -> (select m2 p) = (select m1 p))).


(*Why type*) Definition tag_table: Set ->Set.
Admitted.

(*Why type*) Definition tag_id: Set ->Set.
Admitted.

(*Why logic*) Definition typeof :
  forall (A1:Set), (tag_table A1) -> (pointer A1) -> (tag_id A1).
Admitted.
Implicit Arguments typeof.

(*Why logic*) Definition parenttag :
  forall (A1:Set), (tag_table A1) -> (tag_id A1) -> (tag_id A1) -> Prop.
Admitted.
Implicit Arguments parenttag.

(*Why logic*) Definition subtag :
  forall (A1:Set), (tag_table A1) -> (tag_id A1) -> (tag_id A1) -> Prop.
Admitted.
Implicit Arguments subtag.

(*Why axiom*) Lemma subtag_refl :
  forall (A1:Set),
  (forall (a:(tag_table A1)), (forall (t:(tag_id A1)), (subtag a t t))).
Admitted.

(*Why axiom*) Lemma subtag_parent :
  forall (A1:Set),
  (forall (a:(tag_table A1)),
   (forall (t1:(tag_id A1)),
    (forall (t2:(tag_id A1)),
     (forall (t3:(tag_id A1)),
      ((subtag a t1 t2) -> ((parenttag a t2 t3) -> (subtag a t1 t3))))))).
Admitted.

(*Why predicate*) Definition instanceof (A260:Set) (a:(tag_table A260))
  (p:(pointer A260)) (t:(tag_id A260)) := (subtag a (typeof a p) t).
Implicit Arguments instanceof.

(*Why logic*) Definition downcast :
  forall (A1:Set), (tag_table A1) -> (pointer A1)
  -> (tag_id A1) -> (pointer A1).
Admitted.
Implicit Arguments downcast.

(*Why axiom*) Lemma downcast_instanceof :
  forall (A1:Set),
  (forall (a:(tag_table A1)),
   (forall (p:(pointer A1)),
    (forall (s:(tag_id A1)), ((instanceof a p s) -> (downcast a p s) = p)))).
Admitted.
Implicit Arguments downcast_instanceof.

(*Why logic*) Definition bottom_tag : forall (A1:Set), (tag_id A1).
Admitted.
Set Contextual Implicit.
Implicit Arguments bottom_tag.
Unset Contextual Implicit.

(*Why axiom*) Lemma bottom_tag_axiom :
  forall (A1:Set),
  (forall (a:(tag_table A1)),
   (forall (t:(tag_id A1)), (subtag a t (@bottom_tag A1)))).
Admitted.

(*Why predicate*) Definition fully_packed (A265:Set) (tag_table:(tag_table A265))
  (mutable:(memory A265 (tag_id A265))) (this:(pointer A265))
  := (select mutable this) = (typeof tag_table this).
Implicit Arguments fully_packed.

