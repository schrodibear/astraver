
Require Why.
Require Export PolyList.

(* the Coq pointer list associated to a (finite) linked list *)

Definition plist := (list pointer).

Inductive list_of [t:pointer_store] : pointer -> plist -> Prop :=
  | List_of_null : (list_of t null (nil pointer))
  | List_of_cons : (p:pointer) (is_valid_pointer t p) ->
                   (l:(list pointer))(list_of t (access_pointer t p) l) ->
	           (list_of t p (cons p l)).

Hint list_of : core := Constructors list_of.

(* no common element between two lists *)

Definition disjoint [l1,l2: plist] : Prop :=
  ((x:pointer)(In x l1) -> ~(In x l2)) /\
  ((x:pointer)(In x l2) -> ~(In x l1)).

(* invariance of a list when updating a cell outside of this list *)

Lemma list_of_update_same : 
  (t:pointer_store)(p:pointer)(l:plist)(list_of t p l) -> 
  (p1,p2:pointer) (is_valid_pointer t p1) -> ~(In p1 l) -> 
  (list_of (update_pointer t p1 p2) p l).
Proof.
Induction 1; Intuition.
Apply List_of_cons; Auto.
Rewrite update_access_other_pointer; Auto.
Auto with *.
Red; Intro; Apply H4; Subst p1; Auto with *.
Save.

Lemma no_cycle_1 : (t:pointer_store)(p:pointer)(is_valid_pointer t p) ->
  (l:plist)(list_of t p l) -> ~p=(access_pointer t p).
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

Hints Resolve list_of_update_same list_of_not_in.

(* finite lists characterization *)

Inductive is_list [h: int_store; t: pointer_store] : pointer -> Prop :=
  | List_null : (is_list h t null)
  | List_cons : (p:pointer) (is_valid_int h p) -> (is_valid_pointer t p)
                -> (is_list h t (access_pointer t p)) -> (is_list h t p).

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
  t1=t2 /\ (is_list h2 t2 p2) /\ (access_pointer t2 p2)=p1.

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

