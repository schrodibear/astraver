
Require Why.
Require Export PolyList.

(* the Coq pointer list associated to a (finite) linked list *)

Definition plist := (list pointer).

(* [(lpath t p1 l p2)] :
   there is a path from pointer [p1] to pointer [p2] using links in store [t],
   and the list of pointers along this path is [l]. *)

Inductive lpath [t:pointer_store] : pointer -> plist -> pointer -> Prop :=
  | Path_null : (p:pointer)(lpath t p (nil pointer) p)
  | Path_cons : (p1,p2:pointer) (is_valid_pointer t p1) ->
                (l:(list pointer))(lpath t (pget t p1) l p2) ->
                (lpath t p1 (cons p1 l) p2).

Hint lpath : core := Constructors lpath.

(* [(llist t p l)]: there is a (finite) linked list starting from pointer [p]
   using links in store [t], and this list of pointers is [l] *)

Definition llist [t:pointer_store; p:pointer; l:plist] := (lpath t p l null).

(* no common element between two lists *)

Definition disjoint [l1,l2: plist] : Prop :=
  ((x:pointer)(In x l1) -> ~(In x l2)) /\
  ((x:pointer)(In x l2) -> ~(In x l1)).

(* inductive characterization of [llist] (which could have been an
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

(* invariance of a list when updating a cell outside of this list *)

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

(* [llist] is a function *)

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

(* should go in PolyList *)
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
  ~(length l1)=(length l2) -> ~l1=l2..
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

(***
Lemma no_cycle_1 : (t:pointer_store)(p:pointer)(is_valid_pointer t p) ->
  (l:plist)(list_of t p l) -> ~p=(pget t p).
Proof.
Inversion 2.
Rewrite <- H1 in H; Simpl in H; Tauto.
Subst.
Inversion H0.
Inversion H3.

Save.

Lemma list_of_not_in : 
  (t:pointer_store)(l:plist)(p,p':pointer)
  (list_of t p (cons p' l)) -> ~(In p l).
Proof.
Intros; Inversion H.
Subst.
Inversion H4.
Auto.
Subst.

Save.

Hints Resolve list_of_not_in.
***)

(* finite lists characterization *)

Inductive is_list [h: int_store; t: pointer_store] : pointer -> Prop :=
  | List_null : (is_list h t null)
  | List_cons : (p:pointer) (is_valid_int h p) -> (is_valid_pointer t p)
                -> (is_list h t (pget t p)) -> (is_list h t p).

Hint is_list : core := Constructors is_list.

Lemma is_list_list_of : 
  (h:int_store; t:pointer_store)
  (p:pointer)(is_list h t p) -> (EX l:plist | (list_of t p l)).
Proof.
Intros; Induction H.
Exists (nil pointer); Intuition.
Elim HrecH; Intros.
Exists (cons p x); Intuition.
Save.

(* WF relation over lists *)

Definition Triple := int_store * (pointer_store * pointer).
Definition triple := [h:int_store; t:pointer_store; p:pointer](h, (t, p)).

Definition tl_order [c1,c2:(int_store * (pointer_store * pointer))] : Prop :=
  let (h1,tp1) = c1 in
  let (t1,p1) = tp1 in
  let (h2,tp2) = c2 in
  let (t2,p2) = tp2 in
  t1=t2 /\ (is_list h2 t2 p2) /\ (pget t2 p2)=p1.

Axiom tl_order_wf : (well_founded tl_order).
(**
Lemma tl_order_wf : (well_founded tl_order).
Proof.
Unfold well_founded.
Destruct a; Destruct p; Intros.
Apply Acc_intro.
Destruct y; Destruct p2; Unfold 1 tl_order; Intuition.
Save.
**)

