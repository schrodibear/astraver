Require Import Why.
Require Export caduceus_why.
Require Export List.

(** the Coq pointer list associated to a (finite) linked list *)

Definition plist := list pointer.

Definition in_list := (@In pointer).


Fixpoint pair_in_list (p1:pointer) (p2:pointer)(l:list pointer) {struct l} : Prop :=
  match l with
  | nil => False
  | b :: m => (b = p1 /\ match  m with
                                      | nil => False
                                      | c::n => c = p2
                                      end) 
                                      \/ pair_in_list p1 p2 m
  end.

(** * Paths *)

(** [(reachable t p1 l p2)] :
    there is a path from pointer [p1] to pointer [p2] using links in store [t],
    and the list of pointers along this path is [l]. *)

Inductive reachable (a: alloc_table) (l: memory pointer)(r: memory pointer) : pointer ->  pointer -> Prop :=
  | Path_null : forall p:pointer, reachable a l r p  p
  | Path_left :
      forall p1 p2:pointer,
        valid a p1 ->
          reachable a l r (acc l p1) p2 -> reachable a l r p1  p2
  | Path_right :
      	forall p1 p2:pointer,
        	valid a p1 ->
        	  reachable a l r (acc r p1)  p2 -> reachable a l r p1 p2.
   
Inductive unmarked_reachable (a: alloc_table) (l: memory pointer)(m:memory Z)(r: memory pointer) : pointer ->  pointer -> Prop :=
  | Path_unmarked_null : forall p:pointer, (acc m p) = 0 ->unmarked_reachable a l m r p  p
  | Path_unmarked_left :
      forall p1 p2:pointer,
        valid a p1 ->
          unmarked_reachable a l m r (acc l p1) p2-> (acc m p1) = 0 -> unmarked_reachable a l m r p1  p2
  | Path_unmarked_right :
      	forall p1 p2:pointer,
        	valid a p1 ->
        	  unmarked_reachable a l m r (acc r p1)  p2 -> (acc m p1) = 0-> unmarked_reachable a l m r p1 p2.

Inductive stkOk   (c:memory Z) (l: memory pointer)(r: memory pointer) 
(iL : memory pointer)(iR: memory pointer) : pointer ->  list pointer -> Prop :=
| stkOk_nil : forall t : pointer, stkOk  c l r iL iR t nil 
| stkOk_cons : forall t : pointer, forall p : pointer, forall stk : list pointer,
stkOk  c l r iL iR p stk -> ((acc iL p) = if Zneq_bool (acc c p) 0 then (acc l p) else t) -> 
((acc iR p) = if Zneq_bool (acc c p) 0 then t else (acc r p)) -> 
stkOk  c l r iL iR t (cons p stk).

Inductive clr_list (a: alloc_table)  (c:memory Z) (l: memory pointer)
(r: memory pointer) : pointer ->list pointer-> Prop :=
| clr_list_nil : forall t : pointer , clr_list a c l r t nil 
| clr_list_cons : 
   forall t : pointer, forall p : pointer, forall stack : list pointer, 
     clr_list a c l r p stack -> valid a t ->
       (p = if Zneq_bool (acc c t) 0 then (acc r t) else (acc l t)) ->
          clr_list a c l r t (cons p stack).

Inductive all_in_list (m:memory Z) : list pointer -> Prop :=
| all_in_list_nil : all_in_list m nil 
| all_in_list_cons : forall l : list pointer, forall t : pointer,
all_in_list m l -> (acc m t) <> 0 -> all_in_list m (cons t l).

Lemma reachable_unchanged:forall l0 r0 l r : memory pointer,
(forall x : pointer, (acc r0 x) = (acc r x) /\ (acc l0 x)= (acc l x)) -> 
forall a :alloc_table ,forall root x : pointer , reachable a l0 r0 root x -> reachable a l r root x. 
intros.
induction H0.
constructor.
apply Path_left;auto.
replace (acc l p1) with (acc l0 p1).
auto.
generalize (H p1);intuition.
apply Path_right;auto.
replace (acc r p1) with (acc r0 p1).
auto.
generalize (H p1);intuition.
Qed.

