
Require Why.
Require Export PolyList.

(** the Coq pointer list associated to a (finite) linked list *)

Definition plist := (list pointer).


(** * Paths *)

(** [(lpath t p1 l p2)] :
    there is a path from pointer [p1] to pointer [p2] using links in store [t],
    and the list of pointers along this path is [l]. *)

Inductive lpath [t:pointer_store] : pointer -> plist -> pointer -> Prop :=
  | Path_null : (p:pointer)(lpath t p (nil pointer) p)
  | Path_cons : (p1,p2:pointer) (is_valid_pointer t p1) ->
                (l:(list pointer))(lpath t (pget t p1) l p2) ->
                (lpath t p1 (cons p1 l) p2).

Hint lpath : core := Constructors lpath.


(** * Lists *)

(** [(llist t p l)]: there is a (finite) linked list starting from pointer [p]
    using links in store [t], and this list of pointers is [l] *)

Definition llist [t:pointer_store; p:pointer; l:plist] := (lpath t p l null).

Hints Unfold llist.

(** inductive characterization of [llist] (which could have been an
    inductive definition of [llist])  *)

Lemma llist_null : 
  (t:pointer_store)(p:pointer)(llist t p (nil pointer)) -> p=null.
Proof.
Unfold llist; Inversion 1; Trivial.
Save.

Lemma llist_cons : 
  (t:pointer_store)(p1,p2:pointer)(l:plist)
  (llist t p1 (cons p2 l)) -> p1 = p2 /\ (llist t (pget t p2) l).
Proof.
Unfold llist; Inversion 1; Intuition.
Save.

(** invariance of a list when updating a cell outside of this list *)

Lemma llist_pset_same : 
  (t:pointer_store)(p:pointer)(l:plist)(llist t p l) -> 
  (p1,p2:pointer) (is_valid_pointer t p1) -> ~(In p1 l) -> 
  (llist (pset t p1 p2) p l).
Proof.
Unfold llist; Induction 1; Intuition.
Apply Path_cons; Auto.
Rewrite PointerStore.get_set_other; Auto.
Auto with *.
Red; Intro; Apply H4; Subst p0; Auto with *.
Save.
Hints Resolve llist_pset_same.

(** [llist] is a function *)

Lemma llist_function : 
  (t:pointer_store)(l1,l2:plist)(p:pointer)
  (llist t p l1) -> (llist t p l2) -> l1=l2.
Proof.
Induction l1; Intuition.
Inversion H; Subst.
Inversion H0; Intuition.
Inversion H1.
Inversion H0; Subst.
Inversion H1; Subst.
Inversion H5.
Apply (f_equal ? ? (cons a)).
Apply H with (pget t a); Auto.
Save.

Lemma llist_append : 
  (t:pointer_store)(l1,l2:plist)(p:pointer)
  (llist t p (app l1 l2)) -> 
  (EX p':pointer | (lpath t p l1 p') /\ (llist t p' l2)).
Proof.
Induction l1; Simpl; Intuition.
Exists p; Auto.
Inversion H0; Subst.
Elim (H l2 (pget t a) H6); Intuition.
Exists x; Auto.
Save.

(** this should go in PolyList *)
Lemma In_app_cons : 
  (A:Set)(l:(list A))(x:A) (In x l) -> 
  (EX l1 : (list A) | (EX l2 : (list A) | l = (app l1 (cons x l2)))).
Proof.
Induction l; Simpl; Intuition.
Exists (nil A); Exists l0; Simpl; Subst; Auto.
Elim (H x H1); Clear H; Intros.
Elim H; Clear H; Intuition.
Exists (cons a x0); Exists x1; Simpl; Subst; Auto.
Save.

Lemma list_length_absurd : (A:Set)(l1,l2:(list A))
  ~(length l1)=(length l2) -> ~l1=l2.
Proof.
Induction l1; Induction l2; Simpl; Intuition.
Discriminate H1.
Discriminate H1.
Injection H2; Intros.
Apply (H l0); Intuition.
Save.

Lemma length_app : (A:Set)(l1,l2:(list A))
  (length (app l1 l2)) = (plus (length l1) (length l2)).
Proof.
Induction l1; Simpl; Intuition.
Save.

(** a list starting with [p] does not contain [p] in its remaining elements *)

Lemma llist_not_starting : 
  (t:pointer_store)(p:pointer)(l:plist)
  (llist t (pget t p) l) -> ~(In p l).
Proof.
Red; Intros.
Elim (In_app_cons ? l p H0); Intros.
Elim H1; Clear H1; Intros.
Subst l.
Elim (llist_append t x (cons p x0) (pget t p) H); Intuition.
Inversion H3; Subst.
Generalize (llist_function t x0 (app x (cons p x0)) (pget t p) H8 H).
Intro; Apply (list_length_absurd ? x0 (app x (cons p x0))); Auto.
Rewrite length_app; Simpl; Omega.
Save.


(** * Finite lists characterization *)

Inductive is_list [t: pointer_store] : pointer -> Prop :=
  | List_null : (is_list t null)
  | List_cons : (p:pointer) (is_valid_pointer t p) -> 
                (is_list t (pget t p)) -> (is_list t p).

Hint is_list : core := Constructors is_list.

Lemma is_list_llist : 
  (t:pointer_store)
  (p:pointer)(is_list t p) -> (EX l:plist | (llist t p l)).
Proof.
Intros; Induction H.
Exists (nil pointer); Intuition.
Elim HrecH; Intros.
Exists (cons p x); Intuition.
Save.

Lemma llist_is_list :
  (t:pointer_store)
  (l:plist)(p:pointer)(llist t p l) -> (is_list t p).
Proof.
Induction l; Intuition.
Inversion H; Auto.
Inversion H0; Intuition.
Save.


(** * WF relation over linked lists *)

Definition StorePointerPair := pointer_store * pointer.
Definition store_pointer_pair := [t:pointer_store; p:pointer](t, p).

Definition ll_order [c1,c2: pointer_store * pointer] : Prop :=
  let (t1,p1) = c1 in
  let (t2,p2) = c2 in
  (EX l1:plist | (EX l2:plist | 
    (llist t1 p1 l1) /\ (llist t2 p2 l2) /\ 
    (lt (length l1) (length l2)))).

Axiom ll_order_wf : (well_founded ll_order).
(*
Lemma ll_order_wf : (well_founded ll_order).
Proof.
Unfold well_founded.
Destruct a; Destruct p; Intros.
Apply Acc_intro.
Destruct y; Destruct p2; Unfold 1 ll_order; Intuition.
Save.
*)
Hints Resolve ll_order_wf.


(** * Disjointness *)

(** [disjoint l1 l2]: no common element between lists [l1] and [l2] *)

Definition disjoint [A:Set; l1,l2:(list A)] : Prop :=
  ((x:A)(In x l1) -> ~(In x l2)) /\
  ((x:A)(In x l2) -> ~(In x l1)).
Implicits disjoint.

Section Disjointness.

Variable A : Set.
Variable l1,l2 : (list A).
Variable x : A.

Lemma disjoint_cons : 
  (disjoint l1 (cons x l2)) -> 
  ~(In x l2) ->
  (disjoint (cons x l1) l2).
Proof.
Unfold disjoint; Intuition.
Elim (in_inv H); Intuition.
Subst x; Intuition.
Apply H1 with x0; Intuition.
Elim (in_inv H3); Intuition.
Subst x; Intuition.
Apply H1 with x0; Intuition.
Save.

Lemma disjoint_nil_l : (disjoint (nil A) l2).
Proof.
Unfold disjoint; Intuition.
Save.

Lemma disjoint_l_nil : (disjoint l1 (nil A)).
Proof.
Unfold disjoint; Intuition.
Save.

End Disjointness.
Hints Resolve disjoint_cons disjoint_nil_l disjoint_l_nil.

