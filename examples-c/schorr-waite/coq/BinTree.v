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
| clr_list_cons : forall t : pointer, forall p : pointer, forall stack : list pointer, 
clr_list a c l r p stack -> (p = if Zneq_bool (acc c t) 0 then (acc r t) else (acc l t)) ->
clr_list a c l r t (cons p stack).

Inductive all_in_list (m:memory Z) : list pointer -> Prop :=
| all_in_list_nil : all_in_list m nil 
| all_in_list_cons : forall l : list pointer, forall t : pointer,
all_in_list m l -> (acc m t) <> 0 -> all_in_list m (cons t l).
