Require Import Why.
Require Export caduceus_why.
Require Export List.
Require Export GenericLists.

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

Lemma pair_in_list_in :forall (p1 p2 p3: pointer) ( l : list pointer), pair_in_list p1 p2 (p3::l) -> In p2 l. 
intros.
induction l.
simpl in H.
auto.
simpl in H.
inversion_clear H.
tauto.
auto.
destruct (l).
inversion_clear H.
inversion_clear H0.
subst.
left;auto.
tauto.
intuition;subst;simpl;auto.
inversion_clear H.
left;tauto.
inversion_clear H0.
right;left;tauto.
assert (pair_in_list p1 p2 (p3::p::l)).
right;auto.
clear H.
generalize (IHl H0).
intro.
inversion_clear H.
right;left;auto.
right;right.
auto.
Qed.

(** * Paths *)

(** [(reachable t p1 l p2)] :
    there is a path from pointer [p1] to pointer [p2] using links in store [t],
    and the list of pointers along this path is [l]. *)
Inductive reachable (a: alloc_table) (l: memory pointer)(r: memory pointer) : 
pointer ->  pointer -> list pointer -> Prop :=
  | Path_null : forall p:pointer, reachable a l r p  p nil
  | Path_left :
      forall p1 p2:pointer,
      forall lp : list pointer,
        valid a p1 ->
          reachable a l r (acc l p1) p2 lp-> reachable a l r p1  p2 (p1::lp)
  | Path_right :
      	forall p1 p2:pointer,
      forall lp : list pointer ,
        	valid a p1 ->
        	  reachable a l r (acc r p1)  p2 lp -> reachable a l r p1 p2 (p1::lp). 

Axiom eq_pointer_dec : forall p1 p2 : pointer, {p1 = p2} + {p1 <> p2}.

Fixpoint sans_rep (l:list pointer) {struct l}: Prop :=
match l with
| nil => True
| (a::l) => (if In_dec eq_pointer_dec a l then False else True)  /\ sans_rep l
end.

Lemma split_list : forall  (p : pointer) (path : list pointer), (In p path) ->
exists x : list pointer ,  exists y : list pointer, path = x ++ (p::y).
intros.
induction path.
inversion H.
generalize (in_inv H).
intuition.
exists (nil: list pointer).
exists path.
subst;auto.
inversion H0;inversion H2.
exists (a::x).
exists x0.
subst;auto.
Qed.

Lemma split_reachacle_1 : forall (a : alloc_table)
( l r : memory pointer) (path1: list pointer) (p1 p2 p : pointer) , 
reachable a l r p1 p2 (path1++ p :: nil) -> 
reachable a l r p1 p path1 /\ reachable a l r p p2 (p :: nil).
induction path1.
simpl; intuition.
inversion H; subst; constructor.
inversion H; subst; auto.
simpl; intros.
inversion H; subst.
generalize (IHpath1 (acc l a0) p2 p H5); intuition.
constructor 2; auto.
generalize (IHpath1 (acc r a0) p2 p H5); intuition.
constructor 3; auto.
Qed.

Lemma split_reachable : forall (a : alloc_table) (p1 p2 : pointer) 
( l r : memory pointer) (path2 path1: list pointer), 
reachable a l r p1 p2 (path1++path2) -> exists p3 : pointer , 
reachable a l r p1 p3 path1 /\ reachable a l r p3 p2 path2.
induction path2.
exists p2.
intuition.
rewrite <- app_nil_end in H.
auto.
constructor.
intros.
exists a0.
replace (path1++a0 :: path2) with ((path1++a0::nil)++path2) in H.
generalize (IHpath2 (path1++a0::nil) H).
intros (p3, (hp3a,hp3b)).
generalize (split_reachacle_1 a l r path1 p1 p3 a0 hp3a).
intuition.
inversion H2; subst.
constructor 2; auto.
inversion H6; subst; auto.
constructor 3; auto.
inversion H6; subst; auto.
rewrite app_ass; auto.
Qed.

Lemma split_lists : forall (A:Set)(x:A) l, In x l -> exists l1, exists l2, l = l1 ++ x :: l2.
induction l; simpl; intuition.
exists (nil :list  A); exists l; subst; auto.
elim H; clear H; intros l1 H; elim H; clear H; intros l2 H.
exists (a :: l1); exists l2; subst; auto.
Qed.


Lemma sans_rep_sublist1 : forall (l : list pointer)(p:pointer), sans_rep (p::l) -> 
sans_rep l. 
intros.
destruct H.
apply H0.
Qed.

Lemma sans_rep_sublist : forall (l l1 l2 : list pointer), sans_rep l -> 
l = l1 ++ l2 -> sans_rep l2. 
induction l.
intros.
assert (l1++l2=nil);auto.
generalize (app_eq_nil l1 l2 H1).
intuition;subst;auto.
intros.
destruct l1.
assert (a::l = l2).
auto.
subst;auto.
apply IHl with l1.
apply sans_rep_sublist1 with a;auto.
rewrite <-app_comm_cons in H0.
inversion H0.
auto.
Qed.

Ltac caseq t := generalize (refl_equal t);pattern t at -1;case t.


Lemma sans_rep_p : forall (p1:pointer)(lp:list pointer), sans_rep(p1::lp)->
~In p1 lp.
intros.
simpl in H.
intro.
inversion_clear H.
caseq (In_dec eq_pointer_dec p1 lp).
intros i e.
rewrite e in H1.
elim H1.
intros i.
elim (i H0).
Qed.


Lemma sans_rep_false : forall (p1 : pointer)(lp : list pointer),
sans_rep (p1 :: p1 :: lp) -> False.
intros.
simpl in H.
inversion_clear H.
casetype False.
destruct (In_dec eq_pointer_dec p1 (p1 :: lp));auto.
apply n.
left;auto.
Qed.


Lemma reachable_no_cycle : forall (a : alloc_table) (p1 p2 : pointer) 
( l r : memory pointer) (path : list pointer), reachable a l r p1 p2 (path) -> 
exists path' :list pointer , incl path' path /\ 
sans_rep (path') /\ reachable a l r p1 p2  (path'). 
intros.
induction H.
exists (@nil pointer).
intuition.
simpl;auto.
constructor.
inversion IHreachable.
case (In_dec eq_pointer_dec p1 x).
intro.
generalize (split_list  p1 x i);intro.
inversion_clear H2;inversion_clear H1;inversion_clear H3.
exists (p1::x1).
intuition.
subst.
apply incl_cons.
left;auto.
red.
red in H2.
intros.
right.
apply H2.
apply in_or_app.
right;right;auto.
apply sans_rep_sublist with x x0 ;subst;auto.
generalize (Path_left a l r p1 p2  x H H5).
subst x.
intro.
generalize (split_reachable a p1 p2 l r (p1::x1) (p1::x0) H1).
intros (p3, (Hp3a,Hp3b)).
inversion Hp3b;subst;auto.
intro.
inversion_clear H1.
inversion_clear H3.
exists (p1::x).
split.
apply incl_cons.
left;auto.
red.
red in H2.
intros.
right.
apply H2;auto.
split.
constructor;auto.
case (In_dec eq_pointer_dec p1 x);intuition.
constructor 2;auto.
inversion IHreachable.
case (In_dec eq_pointer_dec p1 x).
intro.
generalize (split_list  p1 x i);intro.
inversion_clear H2;inversion_clear H3.
exists (p1::x1).
inversion_clear H1.
split.
apply incl_cons.
left;auto.
red.
red in H3.
intros.
right.
apply H3.
subst.
apply in_or_app.
right;right;auto.
inversion_clear H4.
split.
apply sans_rep_sublist with x x0 ;subst;auto.
generalize (Path_right a l r p1 p2  x H H5).
subst x.
intro.
generalize (split_reachable a p1 p2 l r (p1::x1) (p1::x0) H2).
intros (p3, (Hp3a,Hp3b)).
inversion Hp3b;subst;auto.
intro.
exists (p1::x).
inversion_clear H1;inversion_clear H3.
split.
apply incl_cons.
left;auto.
red.
red in H2.
intros.
right.
apply H2;auto.
split.
simpl.
case (In_dec eq_pointer_dec p1 x);intuition.
constructor 3;auto.
Qed.

Lemma reachable_in_list : forall (a:alloc_table)(l r: memory pointer)
(p1 p2 : pointer)(lp: list pointer), reachable a l r p1 p2 lp -> 
(exists lp' : list pointer, lp = p1::lp')  \/ lp = nil.
intros.
inversion H;subst.
right.
auto.
left.
exists lp0;auto.
left.
exists lp0;auto.
Qed.


Definition unmarked_reachable (a: alloc_table) (m:memory Z)
(l: memory pointer)(r: memory pointer) (p1:pointer) (p2:pointer): Prop :=
exists lp : list pointer, (forall x : pointer, In x lp -> (acc m x) = 0 ) 
/\ reachable a l r p1 p2 lp.

Inductive stkOk   (c:memory Z) (l: memory pointer)(r: memory pointer) 
(iL : memory pointer)(iR: memory pointer) : pointer ->  list pointer -> Prop :=
| stkOk_nil : forall t : pointer, stkOk  c l r iL iR t nil 
| stkOk_cons : forall t : pointer, forall p : pointer, forall stk : list pointer,
stkOk  c l r iL iR p stk -> ((acc iL p) = if Zneq_bool (acc c p) 0 then (acc l p) else t) -> 
((acc iR p) = if Zneq_bool (acc c p) 0 then t else (acc r p)) -> 
stkOk  c l r iL iR t (cons p stk).

Definition clr_list (a: alloc_table)  (c:memory Z) (l: memory pointer)
(r: memory pointer) : pointer ->list pointer-> Prop :=
let next t := if Z_eq_dec (acc c t) 0 then (acc l t) else (acc r t) in
llist a next .

Inductive all_in_list (m:memory Z) : list pointer -> Prop :=
| all_in_list_nil : all_in_list m nil 
| all_in_list_cons : forall l : list pointer, forall t : pointer,
all_in_list m l -> (acc m t) <> 0 -> all_in_list m (cons t l).

Definition isreachable (a: alloc_table) (l: memory pointer)(r: memory pointer) 
(p1 :pointer) (p2:pointer) : Prop :=
exists lp : list pointer, reachable a l r p1 p2 lp. 
