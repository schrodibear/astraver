Require Import Why.
Require Export caduceus_why.
Require Export List.


Axiom pointer_eq_dec : forall p1 p2:pointer, {p1=p2}+{p1<>p2}.

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
          reachable a l r (acc l p1) p2-> reachable a l r p1  p2
  | Path_right :
      	forall p1 p2:pointer,
        	valid a p1 ->
        	  reachable a l r (acc r p1)  p2 -> reachable a l r p1 p2.


Inductive reachable_no_cycle (a: alloc_table) 
:  memory pointer->memory pointer->pointer-> pointer->list pointer -> Prop :=
  | Path_no_cycle_null : forall l r : memory pointer,forall p2:pointer,
       reachable_no_cycle a l r p2 p2 (p2::nil)
  | Path_no_cycle_left :
      forall l r : memory pointer,
      forall p1 p2:pointer, forall lp : list pointer,
        valid a p1 -> ~ (In p1 lp) ->
        reachable_no_cycle a l r (acc l p1) p2 lp ->
          reachable_no_cycle a l r p1 p2 (p1::lp)
  | Path_no_cycle_right : 
       forall l r : memory pointer,
      	forall p1 p2:pointer, forall lp : list pointer,
        	valid a p1 -> ~ (In p1 lp) ->
                  reachable_no_cycle a l r (acc r p1) p2 lp -> 
                  reachable_no_cycle a l r p1 p2 (p1::lp).
   
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
generalize (H p1);intuition.
replace (acc l p1) with (acc l0 p1);auto. 
generalize (H p1);intuition.
apply Path_right;auto.
replace (acc r p1) with (acc r0 p1);auto.
Qed.


Lemma mem : forall (x:pointer) l, {In x l}+{~ In x l}.
induction l;simpl;auto.
elim (pointer_eq_dec a x).
intro;left;left;auto.
intro ne1;elim IHl.
intro e2;left;right;auto.
tauto.
Qed.

Section acyclic_path.

Variable a: alloc_table.
Variables l r: memory pointer.
Axiom T:False.

(*Lemma concat : forall (p1 p2 p3: pointer) list,~(In p1 list)-> reachable_no_cycle a l r p1 p2 list ->
reachable_no_cycle a l r p2 p3 list -> reachable_no_cycle a l r p1 p3 list.
intros.
induction H0;auto.
apply Path_no_cycle_left;auto.
apply IHreachable_no_cycle.
intuition.
apply H2.
unfold In in H4;intuition.
inversion H3.

*)

(*
Lemma affaibli : forall (lp:list pointer) (p1 p2:pointer), reachable_no_cycle a l r p1 p2 lp ->
 reachable_no_cycle a l r p1 p2 nil.
fix 4.
intros lp p1 p2 H;inversion H.
intros;constructor.
constructor 2;auto.
apply (affaibli _ _ _ H2).
intros;constructor 2;[auto|auto|idtac]. 
exact H2.
apply affaibli with lp.
intros;constructor 3;[auto|auto|idtac].
exact H2.
Qed.

inversion H1;subst.
constructor.
apply H1.
generalize lp H1;clear IHreachable_no_cycle H1 H0 lp;induction lp;auto.
intros;apply IHlp.

induction lp.
auto.
intros;apply IHlp.
inversion H;subst.
constructor.
constructor 2;auto.
intro;apply H1;simpl;right;auto. 


intro H3;destruct H3.
intro H0;induction H0.
constructor.
constructor 2;auto.
generalize (IHreachable_no_cycle IHlp); clear IHreachable_no_cycle;intro reach.
intros;constructor 2.
auto.
*)
Scheme Reach_ind := Induction for reachable_no_cycle Sort Prop.

Inductive Tail (A:Set): list A -> list A -> Prop:=
Tail_id : forall l,Tail A l l
|Tail_cons : forall a l m, Tail A l m -> Tail A l (a::m).

Implicit Arguments Tail [A].
Implicit Arguments Tail_id [A].
Implicit Arguments Tail_cons [A].

Fixpoint chop_until_last (p:pointer) (lp:list pointer) {struct lp} : list pointer:=
match lp with
nil => nil
| x::q => if mem p q then chop_until_last p q else p::q
end. 

Fixpoint last (A:Set) (a:A) (l:list A) {struct l}:A :=
match l with
nil => a
| x::q => last A a q
end.

Implicit Arguments last [A].

Lemma chop_path : forall visited p,In p visited ->
reachable_no_cycle a l r p (last p visited) (chop_until_last p visited).
induction visited.
simpl;intros p H;elim H.
simpl last.
simpl chop_until_last.
intro p;destruct (mem p visited).
intro.
apply IHvisited;auto.
intro H;destruct H.
clear a0 H IHvisited.
generalize visited n;clear visited n.
induction visited.
intros;constructor 1.
intuition.

(*simpl.
intros.
assert (H1:p<>p0).
tauto.
assert (H2:~In p0 visited).
tauto.*)
intros p0 H.
apply chop_path;auto.
intuition.

Qed.

Lemma remove_cycle: forall p1 p2, reachable a l r p1 p2 -> 
exists visited:list pointer,
 (forall p0,In p0 visited -> 
(exists lp, reachable_no_cycle a l r p0 p2 lp)) ->
(reachable_no_cycle a l r p1 p2 visited).
intros p1 p2 R.
induction R.
exists (p::nil). 
intros;constructor.
destruct IHR.
elim (mem p1 x).
Focus 2.
intro notIn;exists (p1::x);intros;constructor 2;auto.
apply H0.
intros.
simpl In in H1.
destruct (H1 p0 (or_intror (p1=p0) H2)).
exists x0.
assumption.
Focus 2.
destruct IHR.
elim (mem p1 x).
Focus 2.
intro notIn;exists (p1::x);intros;constructor 3;auto.
apply H0.
intros.
simpl In in H1.
destruct (H1 p0 (or_intror (p1=p0) H2)).
exists x0.
assumption.
intro.
exists x.
intro.
generalize (H0 H2);intro.

auto.
inversion H3.
rewrite H6 in H4.
inversion H4.
rewrite H10 in H2;rewrite H12 in H2;elim (notIn H2).
exists (p1::lp).
subst lp.
split.
constructor.
destruct x;inversion H15.

constructor 2.
auto.
exists x0;split;auto.
destruct H3.
inversion H3.

constructor 2.

(* lemme : si reachable l alors reachable nil *)
intros;elim (mem (acc l p0) visited).
intro H2;generalize (H1 (acc l p0) H2);intro H3;apply IHR;auto.
elim T. (* lemme: ajout d'une etape \u00e0 la fin d'un chemin *)
intros;elim (mem (acc r p0) visited).
intro H2;generalize (H1 (acc r p0) H2);intro H3;apply IHR;auto.
elim T. (* lemme: ajout d'une etape \u00e0 la fin d'un chemin *)
 




Lemma reachable_reachable_no_cycle : forall  (a: alloc_table)
 (l: memory pointer)(r: memory pointer) (p1 p2:pointer) ,
reachable a l r p1 p2 -> reachable_no_cycle a l r p1 p2 nil.
intros.

induction H.
apply Path_no_cycle_null.

apply Path_no_cycle_left;auto.



Lemma reachable_no_cylce_reachable : forall  (a: alloc_table)
 (l: memory pointer)(r: memory pointer) (p1 p2:pointer) ,
reachable_no_cycle a l r p1 p2 -> reachable a l r p1 p2.
intros.
induction H.
apply Path_null.
apply Path_left;auto.




(*Lemma reachable_lnoloop : forall a : alloc_table, forall l r : memory pointer , 
forall p x :pointer, x<>p -> reachable a l r x (acc l p) -> (acc l p) <> p.
intros.
inversion H0; subst; auto.
intuition.
apply H2.
rewrite H4; auto.
intuition.
apply H2.
rewrite H4; auto.


Lemma reachable_rnull : forall a : alloc_table, forall l r : memory pointer , 
forall p x :pointer,reachable a l r x (acc l p) -> reachable a l (upd r p null) x (acc l p).
intros.
inversion H.
constructor.


apply Path_left;subst;auto.

apply Path_right.
auto.
*)


