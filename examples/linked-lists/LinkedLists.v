
Require Why.

(* finite lists characterization *)

Inductive is_list [h: int_store; t: pointer_store] : pointer -> Prop :=
  | List_null : (is_list h t null)
  | List_cons : (p:pointer) (is_valid_int h p) -> (is_valid_pointer t p)
                -> (is_list h t (access_pointer t p)) -> (is_list h t p).

Hint is_list : core := Constructors is_list.

(* the Coq pointer list associated to a (finite) linked list *)

Require PolyList.

Definition plist := (list pointer).

Inductive list_of [t:pointer_store] : pointer -> plist -> Prop :=
  | List_of_null : (list_of t null (nil pointer))
  | List_of_cons : (p:pointer) (is_valid_pointer t p) ->
                   (l:(list pointer))(list_of t (access_pointer t p) l) ->
	           (list_of t p (cons p l)).

Hint list_of : core := Constructors list_of.

Lemma is_list_list_of : 
  (h:int_store; t:pointer_store)
  (p:pointer)(is_list h t p) -> (EX l:plist | (list_of t p l)).
Proof.
Intros; Induction H.
Exists (nil pointer); Intuition.
Elim HrecH; Intros.
Exists (cons p x); Intuition.
Save.

Definition disjoint [l1,l2: plist] : Prop :=
  ((x:pointer)(In x l1) -> ~(In x l2)) /\
  ((x:pointer)(In x l2) -> ~(In x l1)).

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

