(* Load Programs. *)
Require Import Why.
Require Export caduceus_why.
Require Export List.

(** the Coq pointer list associated to a (finite) linked list *)

Definition plist := list pointer.

(** * Paths *)

(** [(lpath t p1 l p2)] :
    there is a path from pointer [p1] to pointer [p2] using links in store [t],
    and the list of pointers along this path is [l]. *)

Inductive lpath (a: alloc_table) (next: pointer -> pointer) : pointer -> plist -> pointer -> Prop :=
  | Path_null : forall p:pointer, lpath a next p nil p
  | Path_cons :
      forall p1 p2:pointer,
        valid a p1 ->
        forall l:list pointer,
          lpath a next (next p1) l p2 -> lpath a next  p1 (cons p1 l) p2.

Hint Constructors lpath.

Lemma lpath_eq_fun : forall (a: alloc_table) (f g :pointer -> pointer) (p q: pointer) 
(l : list pointer),
 (forall p, In p l -> f p = g p) ->
 lpath a f p l q  -> lpath a g p l q
.
intros.
induction H0.
constructor.
constructor.
auto.
rewrite <-  H.
apply IHlpath.
intros.
apply H.
right;auto.
left;auto.
Qed.

(** * Lists *)

(** [(llist t p l)]: there is a (finite) linked list starting from pointer [p]
    using links in store [t], and this list of pointers is [l] *)

Definition llist (a: alloc_table) (next : pointer -> pointer) (p:pointer) (l:plist) :=
  lpath a next p l null.

Hint Unfold llist .

(** inductive characterization of [llist] (which could have been an
    inductive definition of [llist])  *)

Lemma llist_null :
 forall (a: alloc_table) (next : pointer -> pointer) (p:pointer), llist a next p nil -> p = null.
Proof.
unfold llist; inversion 1; trivial.
Qed.

Lemma llist_cons :
 forall (a: alloc_table) (next : pointer-> pointer) (p1 p2:pointer) (l:plist),
   llist a next p1 (cons p2 l) -> p1 = p2 /\ llist a next (next p2) l.
Proof.
unfold llist; inversion 1; intuition.
Qed.

(** invariance of a list when updating a cell outside of this list *)
(*
Lemma llist_pset_same :
 forall (a: alloc_table) (next : pointer -> pointer) (p:pointer) (l:plist),
   llist a next p l ->
   forall p1 p2:pointer,
     ~ In p1 l -> llist a (upd t p1 p2) p l.
Proof.
unfold llist; simple induction 1; intuition.
apply Path_cons; auto.
 rewrite acc_upd_neq; auto.
auto with *.
red; intro; apply H3; subst p0; auto with *.
Qed.
Hint Resolve llist_pset_same .
*)
(** [llist] is a function *)

Lemma llist_function :
 forall (a a': alloc_table) (next : pointer-> pointer) (l1 l2:plist) (p:pointer),
   llist a next p l1 -> llist a' next p l2 -> l1 = l2.
Proof.
simple induction l1; intuition.
inversion H; subst.
inversion H0; intuition.
inversion H1; elim H6; auto.
inversion H0; subst.
inversion H1; subst.
inversion H0.
inversion H3; elim H9; auto.
apply (f_equal (cons a0)).
apply H with (next a0); auto.
Qed.

Lemma llist_append :
 forall (a: alloc_table) (next : pointer -> pointer) (l1 l2:plist) (p:pointer),
   llist a next p (app l1 l2) ->
    exists p' : pointer, lpath a next p l1 p' /\ llist a next p' l2.
Proof.
simple induction l1; simpl; intuition.
exists p; auto.
inversion H0; subst.
elim (H l2 (next a0) H6); intuition.
exists x; auto.
Qed.

(** this should go in PolyList *)
Lemma In_app_cons :
 forall (A:Set) (l:list A) (x:A),
   In x l ->
     exists l1 : list A, exists l2 : list A, l = app l1 (cons x l2).
Proof.
simple induction l; simpl; intuition.
exists (nil (A:=A)); exists l0; simpl; subst; auto.
elim (H x H1); clear H; intros.
elim H; clear H; intuition.
exists (cons a x0); exists x1; simpl; subst; auto.
Qed.

Lemma list_length_absurd :
 forall (A:Set) (l1 l2:list A), length l1 <> length l2 -> l1 <> l2.
Proof.
simple induction l1; simple induction l2; simpl; intuition.
discriminate H1.
discriminate H1.
injection H2; intros.
apply (H l0); intuition.
Qed.

Lemma length_app :
 forall (A:Set) (l1 l2:list A),
   length (app l1 l2) = (length l1 + length l2)%nat.
Proof.
simple induction l1; simpl; intuition.
Qed.

(** a list starting with [p] does not contain [p] in its remaining elements *)

Lemma llist_not_starting :
 forall (a: alloc_table) (next: pointer -> pointer) (p:pointer) (l:plist),
   llist a next (next p) l -> ~ In p l.
Proof.
red; intros.
elim (In_app_cons _ l p H0); intros.
elim H1; clear H1; intros.
subst l.
elim (llist_append a next x (cons p x0) (next p) H); intuition.
inversion H3; subst.
generalize (llist_function a a next x0 (app x (cons p x0)) (next p) H8 H).
intro; apply (list_length_absurd _ x0 (app x (cons p x0))); auto.
rewrite length_app; simpl; omega.
Qed.

Lemma llist_no_rep: forall (a : alloc_table)(next : pointer->pointer)(p q : pointer) 
(l : list pointer) , llist a next p (q :: l) -> p=q /\ ~ In p l.
unfold llist.
intros.
inversion H.
subst.
split;auto.
apply llist_not_starting with a next.
auto.
Qed.

(** * Finite lists characterization *)

Inductive is_list (a: alloc_table) (next: pointer-> pointer) : pointer -> Prop :=
  | List_null : is_list a next null
  | List_cons :
      forall p:pointer,
        valid a p -> is_list a next (next p) -> is_list a next p.

Hint Constructors is_list.

Lemma is_list_llist :
 forall (a: alloc_table) (next: pointer-> pointer) (p:pointer),
   is_list a next p -> exists l : plist, llist a next p l.
Proof.
intros; elim H.
exists (nil (A:=pointer)); intuition.
intros; elim H2; intros.
exists (cons p0 x); intuition.
Qed.

Lemma llist_is_list :
 forall (a: alloc_table) (next: pointer-> pointer) (l:plist) (p:pointer),
   llist a next p l -> is_list a next p.
Proof.
simple induction l; intuition.
inversion H; auto.
inversion H0; intuition.
Qed.


(** * WF relation over linked lists *)

Definition Length := ((memory pointer) * pointer)%type.
Definition length (a: alloc_table) (t: memory pointer) (p:pointer) := (t, p).

Definition length_order (c1 c2: memory pointer * pointer) : Prop :=
  let (t1, p1) := c1 in
  let (t2, p2) := c2 in
    exists a : alloc_table,
    exists l1 : plist,
    exists l2 : plist,
    llist a (acc t1) p1 l1 /\ llist a (acc t2) p2 l2 /\ (List.length l1 < List.length l2)%nat.

Lemma length_order_wf : well_founded length_order.
Proof.
apply well_founded_inv_lt_rel_compat with
 (F := fun (x:Length) n =>
         let (t, p) := x in 
         exists a : alloc_table,
         exists l : plist, llist a (acc t) p l /\ List.length l = n).
unfold length_order, inv_lt_rel.
simple destruct x; simple destruct y; intuition.
elim H; clear H; intros a H; elim H; clear H; 
intros l1 H; elim H; clear H; intros l2 H.
intuition.
exists (List.length l1).
exists a; exists l1; intuition.
intuition.
elim H1; clear H1; intros a0 H1; elim H1; intros l2'; intuition.
generalize (llist_function a a0 _ _ _ _ H H4); intro; subst l2.
omega.
Qed.
Hint Resolve length_order_wf .

Lemma length_acc :
  forall a tl p,
  is_list a (acc tl) p -> p <> null ->
  length_order (length a tl (acc tl p)) (length a tl p).
Proof.
unfold length,length_order; intros.
exists a.
inversion H; intuition.
absurd (p = null); auto.
subst p0.
generalize (is_list_llist _ _ _ H2).
intros [l1 Hl1]; exists l1.
generalize (is_list_llist _ _ _ H).
intros [l2 Hl2]; exists l2.
intuition.
inversion Hl2.
absurd (p = null); auto.
assert (l1 = l).
apply llist_function with a a (acc tl) (acc tl p); auto.
subst; auto.
Qed.
Hint Resolve length_acc.


(** * Disjointness *)

(** [disjoint l1 l2]: no common element between lists [l1] and [l2] *)

Definition disjoint (A:Set) (l1 l2:list A) : Prop :=
  (forall x:A, In x l1 -> ~ In x l2) /\
  (forall x:A, In x l2 -> ~ In x l1).
Implicit Arguments disjoint.

Section Disjointness.

Variable A : Set.
Variables l1 l2 : list A.
Variable x : A.

Lemma disjoint_cons :
 disjoint l1 (cons x l2) -> ~ In x l2 -> disjoint (cons x l1) l2.
Proof.
unfold disjoint; intuition.
elim (in_inv H); intuition.
subst x; intuition.
apply H1 with x0; intuition.
elim (in_inv H3); intuition.
subst x; intuition.
apply H1 with x0; intuition.
Qed.

Lemma disjoint_nil_l : disjoint nil l2.
Proof.
unfold disjoint; intuition.
Qed.

Lemma disjoint_l_nil : disjoint l1 nil.
Proof.
unfold disjoint; intuition.
Qed.

End Disjointness.
Hint Resolve disjoint_cons disjoint_nil_l disjoint_l_nil .

(** * Cyclicity *)

Section Cyclicity.

Variable a : alloc_table.
Variable tl : pointer -> pointer.

Definition finite (p : pointer) :=
  exists r : plist, 
  forall p', 
  (exists lpp', lpath a tl p lpp' p') -> p'<>null -> valid a p' /\ In p' r.

Lemma finite_is_valid : forall p, p<>null -> finite p -> valid a p.
Proof.
unfold finite; intuition.
elim H0; clear H0; intuition.
assert (h : exists lpp' : plist, lpath a tl p lpp' p).
exists (@nil pointer); auto.
generalize (H0 p h); clear H0; intuition.
Save.

Definition cyclic (p : pointer) :=
  exists l1:plist, exists l2:plist, exists p',
  p'<>null /\ lpath a tl p l1 p' /\ lpath a tl p' l2 p'.

(** [cyclic] and [is_list] are exclusive *)
Lemma cyclic_is_list_exclusive : forall p,
  cyclic p -> is_list a tl p -> False.
Proof.
intros.
elim H; clear H; intros l1 H; elim H; clear H; intros l2 H;
elim H; clear H; intros p'; intuition.
elim (is_list_llist a tl p H0); clear H0; intros l0 Hl0.
unfold llist in Hl0.
Admitted.

(** when a list is finite, it is either [cyclic] or [is_list] *)
Lemma finite_cyclic_or_is_list : forall p, 
  finite p -> cyclic p \/ is_list a tl p.
Proof.
Admitted.

End Cyclicity.

