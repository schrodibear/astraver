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

Lemma sans_rep_sublist2 : forall (l l1 l2 : list pointer) ( a : pointer), sans_rep l -> 
l = l1 ++a::l2 -> sans_rep (l1++l2). 
induction l.
intros.
destruct l1.
simpl in H0.
inversion H0.
inversion H0.
intros.
induction l1.
simpl in *|-*.
apply sans_rep_sublist1 with a.
inversion H0;subst.
auto.
inversion H0.
subst.
unfold sans_rep.
simpl.
elim H.
intros.
destruct (In_dec eq_pointer_dec a1 (l1 ++ a0::l2) ) .
inversion H1.
destruct (In_dec eq_pointer_dec a1 (l1 ++ l2)).
elim n.
elim (in_app_or _ _ _ i).
intro; apply in_or_app; auto.
intro; apply in_or_app; intuition.
intuition.
apply IHl with a0;auto.
Qed.

Lemma sans_rep_sublist_bis : forall (l2 l l1  : list pointer), sans_rep l -> 
l = l1 ++ l2 -> sans_rep l1. 
induction l2.
intros.
subst.
rewrite <- app_nil_end in H.
auto.
intros.
subst.
assert ((l1 ++ a :: l2) = (l1 ++ a :: l2)).
auto.
generalize (sans_rep_sublist2 (l1 ++ a :: l2) l1 l2 a H H0).
intro.
apply IHl2 with (l1++l2);auto.
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

Lemma sans_rep_false2 : forall (p1 : pointer)(lp1 lp2 : list pointer),
sans_rep (p1 ::lp1 ++ p1 :: lp2) -> False.
intros.
simpl in H.
inversion_clear H.
destruct (In_dec eq_pointer_dec p1 (lp1 ++ p1 :: lp2)).
inversion H0.
apply n;clear n.
clear H1.
induction lp1.
simpl;left;auto.
right;auto.
Qed.

Lemma sans_rep_p_bis : forall (p1:pointer)(lp1 lp2:list pointer), sans_rep(lp1++p1::lp2)->
~In p1 lp1.
intros.
intro.
induction lp1.
inversion H0.
generalize (eq_pointer_dec a p1).
intros [p|p].
subst.
apply sans_rep_false2 with p1 lp1 lp2;auto.
apply IHlp1.
apply sans_rep_sublist1 with a;auto.
inversion H0.
elim (p H1).
auto.
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

(* WF relation over graph *)

Record var_type : Set := mkvar_type
  { a : alloc_table;
    m : memory Z;
    c : memory Z;
     l : memory pointer;
     r : memory pointer;
     p : pointer;
     t : pointer
    }.

Definition reachable_elements (a:alloc_table) (l r:memory pointer) (p t: pointer)
(lp : list pointer):Prop :=
sans_rep lp/\
forall p2 : pointer ,p2<> null-> (isreachable a l r p p2 \/isreachable a l r t p2) <-> In p2 lp.

Fixpoint mesure_mark (m : memory Z) (l : list pointer) {struct l} : nat :=
match l with
| nil => 0%nat
| p::l => plus ( if Z_eq_dec (acc m p) 0 then 1%nat else 0%nat) (mesure_mark m l)
end.

Lemma mesure_mark_a : forall m : memory Z , forall lp1a lp1b : list pointer,
(plus (mesure_mark m lp1a) (mesure_mark m lp1b))  = mesure_mark m (lp1a++lp1b).
intros.
induction lp1a.
simpl;auto.
case (Z_eq_dec (acc m0 a0) 0).
simpl.
intros.
replace (acc m0 a0) with 0;auto.
simpl.
apply (f_equal S).
auto.
simpl.
intros.
intuition.
Qed.

Lemma mesure_mark_b : forall p : pointer , forall lp1 lp2a lp2b : list pointer ,
sans_rep (p::lp1)-> sans_rep (lp2a++p::lp2b)->
(forall q : pointer , In q (p::lp1) -> In q (lp2a++p::lp2b)) ->
(forall q : pointer, In q lp1 -> In q (lp2a ++ lp2b)).
intros.
case (eq_pointer_dec q p0).
intro.
subst.
generalize  (sans_rep_p p0 lp1 H).
intuition.
intro.
assert (In q (lp2a ++ p0 :: lp2b) -> In q (lp2a++lp2b)).
intros.
apply in_or_app.
generalize (in_app_or lp2a (p0::lp2b) q H3) .
intros [H4|H4].
left;auto.
destruct H4.
elim (n );auto.
right;auto.
apply H3.
apply H1.
right;auto.
Qed.

Lemma sans_rep_sublist3 : forall (l l1 l2 : list pointer) ( a : pointer), sans_rep l -> 
l = l1 ++a::l2 -> sans_rep (a::l1++l2). 
induction l0.
intros.
destruct l1.
simpl in H0.
inversion H0.
inversion H0.
intros.
destruct l1.
simpl in *|-*.
inversion H.
inversion H0;subst;auto.
inversion H0;subst.
rewrite <- app_comm_cons.
inversion H.
case (In_dec eq_pointer_dec p0 (a1 :: l1 ++ l2));intros.
destruct (In_dec eq_pointer_dec p0 (l1 ++ a1 :: l2));intros.
inversion H1.
elim n.
apply in_or_app.
rewrite app_comm_cons in i.
generalize (in_app_or (a1:: l1) l2 p0 i).
intuition.
generalize (in_inv H4).
intuition.
right;left;auto.
rewrite <- app_comm_cons in H0.
assert (l1 ++ a1 :: l2 = l1 ++ a1 :: l2).
auto.
generalize (IHl0 l1 l2 a1 H2 H3).
intro.
simpl.
case (In_dec eq_pointer_dec a1 (p0 :: l1 ++ l2));intro.
inversion i.
subst.
elim n.
left;auto.
inversion H4.
destruct (In_dec eq_pointer_dec a1 (l1 ++ l2)).
inversion H6.
elim (n0 H5).
split;auto.
split.
destruct (In_dec eq_pointer_dec p0 (l1 ++ l2)).
elim n.
right;auto.
auto.
apply sans_rep_sublist1 with a1;auto.
Qed.

Lemma mesure_mark_c : forall p : pointer , forall lp1 lp2a lp2b : list pointer ,
sans_rep (p::lp1)-> sans_rep (lp2a++p::lp2b)->
(forall q : pointer ,  In q (lp2a++p::lp2b)->In q (p::lp1) ) ->
(forall q : pointer,  In q (lp2a ++ lp2b)->In q lp1 ).
intros.
case (eq_pointer_dec q p0).
intro.
subst.
assert (lp2a ++ p0 :: lp2b = lp2a ++ p0 :: lp2b).
auto.
generalize (sans_rep_sublist2 (lp2a ++ p0 :: lp2b) lp2a lp2b p0 H0 H3);intro.
generalize (sans_rep_sublist (lp2a++p0::lp2b) lp2a (p0::lp2b)  H0).
intros.
generalize (sans_rep_sublist3 (lp2a ++ p0 :: lp2b) lp2a lp2b p0 H0 H3).
intro.
inversion H6.
destruct (In_dec eq_pointer_dec p0 (lp2a ++ lp2b)).
inversion H7.
elim ( n H2).
intro.
assert (In q (lp2a ++ p0 :: lp2b)).
generalize ( in_app_or lp2a lp2b q H2).
intuition.
generalize (H1 q H3);intro.
inversion H4.
elim (n ).
auto.
auto.
Qed.

Lemma mesure_mark_bbis : forall (l1 l2 : list pointer) ( m : memory Z), 
mesure_mark m (l1++l2) = plus (mesure_mark m l1) (mesure_mark m l2).
intros.
induction l1.
simpl;auto.
simpl.
destruct (Z_eq_dec (acc m0 a0) 0).
replace (acc m0 a0) with 0;auto.
simpl.
apply (f_equal S).
auto.
simpl.
auto.
Qed.


Lemma mesure_mark_bis : forall m : memory Z,forall lp1 lp2 : list pointer , (forall p : pointer, 
In p lp1 -> In p lp2)-> (forall p : pointer, In p lp2 -> In p lp1) ->sans_rep lp1 -> sans_rep lp2->mesure_mark m lp1 = mesure_mark m lp2.
intros m0 lp1.
induction lp1.
destruct lp2.
auto.
assert (In p0 (p0::lp2)).
left;auto.
intros.
elim (H1 p0 H).
assert ( In a0 (a0::lp1)).
left;auto.
intros.
generalize (H0 a0 H).
intro.
generalize (split_list a0 lp2 H4). 
intros (lp2a,(lp2b,sub)).
subst.
generalize ( mesure_mark_a m0 lp2a (a0::lp2b)).
intro.
replace (mesure_mark m0 (lp2a ++ a0 :: lp2b)) with (mesure_mark m0 lp2a + mesure_mark m0 (a0 :: lp2b))%nat;auto.
assert (mesure_mark m0 lp1 = mesure_mark m0 (lp2a++lp2b)).
apply IHlp1.
apply mesure_mark_b with a0;auto .
apply mesure_mark_c with a0;auto .
apply sans_rep_sublist1 with a0;auto.
apply (sans_rep_sublist2 (lp2a ++ a0 :: lp2b) lp2a lp2b a0 H3) .
auto.
simpl.
destruct (Z_eq_dec (acc m0 a0)).
simpl.
rewrite <- plus_n_Sm.
rewrite H6.
apply (f_equal S).
apply mesure_mark_bbis.
simpl.
rewrite H6.
apply mesure_mark_bbis.
Qed.

Lemma reacha_element : forall (a:alloc_table) (l r:memory pointer) (p t: pointer) (m : memory Z),
  forall lp1 lp2,reachable_elements a l r p t lp1 /\ reachable_elements a l r p t lp2 ->
  (forall (q : pointer) , In q lp1 <-> In q lp2).
intuition;inversion_clear H0;inversion_clear H1;generalize (H3 q);generalize (H4 q);
intuition.
Qed.


Lemma mesure_mark_function : 
  forall (a:alloc_table) (l r:memory pointer) (p t: pointer) (m : memory Z),
  forall lp1 lp2,
reachable_elements a l r p t lp1 /\ reachable_elements a l r p t lp2
-> mesure_mark (m : memory Z) lp1 = mesure_mark (m : memory Z) lp2.
intros.
generalize (reacha_element a0 l0 r0 p0 t0 m0 lp1 lp2 H).
intro.
apply mesure_mark_bis;intros.
generalize (H0 p1);intuition.
generalize (H0 p1);intuition.
inversion_clear H.
inversion H1;auto.
inversion_clear H.
inversion H2;auto.
Qed.

Definition order_mark_m  (e1 e2 : var_type): Prop :=
exists lp1 : list pointer,
  exists lp2 : list pointer,
    reachable_elements e1.(a) e1.(l) e1.(r) e1.(p) e1.(t) lp1 /\ 
    reachable_elements e2.(a) e2.(l) e2.(r) e2.(p) e2.(t) lp2 /\
lt (mesure_mark e1.(m) lp1)  (mesure_mark e2.(m) lp2).

Definition order_mark_c  (e1 e2 : var_type): Prop :=
exists lp1 : list pointer,
  exists lp2 : list pointer,
    reachable_elements e1.(a) e1.(l) e1.(r) e1.(p) e1.(t) lp1 /\ 
    reachable_elements e2.(a) e2.(l) e2.(r) e2.(p) e2.(t) lp2 /\ 
lt (mesure_mark e1.(c) lp1)  (mesure_mark e2.(c) lp2).

Definition order_pile (e1 e2 : var_type) : Prop :=
exists pile1 : list pointer,
    exists pile2 : list pointer,
      clr_list e1.(a) e1.(c) e1.(l) e1.(r) e1.(p) pile1 /\ 
      clr_list e2.(a) e2.(c) e2.(l) e2.(r) e2.(p) pile2 /\ 
       lt (List.length pile1)  (List.length pile2).

Require Export Lexicographic_Product.
Require Import Relation_Operators.


Lemma order_mark_m_wf : well_founded order_mark_m.
Proof.
apply well_founded_inv_lt_rel_compat with (fun (e1:var_type) (n : nat) 
=>
exists lp1 : list pointer ,
    reachable_elements e1.(a) e1.(l) e1.(r) e1.(p) e1.(t) lp1 /\
    n = mesure_mark e1.(m) lp1).
unfold order_mark_m,inv_lt_rel.
intros x y (pile1,(pile2,H)).
exists (mesure_mark (m x) pile1).
exists pile1.
intuition.
intro.
intros (pile3,(H1,H2)).
intuition.
subst m0.
assert ((mesure_mark (m y) pile3) = (mesure_mark (m y) pile2)).
apply (mesure_mark_function (a y) (l y) (r y) (p y) (t y) (m y) pile3 pile2).
split;auto.
rewrite H2.
auto.
Qed.

Lemma order_mark_c_wf : well_founded order_mark_c.
Proof.
apply well_founded_inv_lt_rel_compat with (fun (e1:var_type) (n : nat) 
=>
exists lp1 : list pointer ,
    reachable_elements e1.(a) e1.(l) e1.(r) e1.(p) e1.(t) lp1 /\
    n = mesure_mark e1.(c) lp1).
unfold order_mark_c,inv_lt_rel.
intros x y (pile1,(pile2,H)).
exists (mesure_mark (c x) pile1).
exists pile1.
intuition.
intro.
intros (pile3,(H1,H2)).
intuition.
subst m0.
assert ((mesure_mark (c y) pile3) = (mesure_mark (c y) pile2)).
apply (mesure_mark_function (a y) (l y) (r y) (p y) (t y) (c y) pile3 pile2).
split;auto.
rewrite H2.
auto.
Qed.

(*
Lemma order_pile_wf : well_founded order_pile.
Proof.
apply well_founded_inv_lt_rel_compat with (fun (e1:var_type) (n : nat) 
=>
exists pile1 : list pointer ,
(clr_list e1.(a) e1.(c) e1.(l) e1.(r) e1.(p) pile1 /\ n=(List.length pile1))).
unfold order_pile,inv_lt_rel.
intros x y (pile1,(pile2,H)).
exists (List.length pile1).
exists pile1.
intuition.
intro.
intros (pile3,(H1,H2)).
intuition.
subst m0.
replace pile3 with pile2;intuition .
Print clr_list.
apply llist_function with (next :=(fun t : pointer => if Z_eq_dec (acc (c y) t) 0 then acc (l y) t else acc (r y) t))
( a := (a y)) (a' := (a y)) (p:= (p y));trivial.
Qed.
*)

Section lexico.

Variables A B : Set.

Variable Ra : A -> A -> Prop.
Variable Rb : B -> B -> Prop.

Definition lex := lexprod A (fun _:A => B) Ra (fun _:A => Rb).

Lemma lex_well_founded :
 well_founded Ra -> well_founded Rb -> well_founded lex.
Proof.
intros wfa wfb.
exact
 (wf_lexprod A (fun _:A => B) Ra (fun _:A => Rb) wfa (fun _ => wfb)).
Qed.

End lexico.

Section LT_WF_REL.
Variable A : Set.

Variable X : Set.
Variable lt : X -> X -> Prop.
Variable F : A -> X -> Prop.
Definition inv_lt_rel x y :=
   exists2 n : _, F x n & (forall m, F y m -> lt n m).

Hypothesis lt_wf : well_founded lt.

Remark acc_lt_rel : forall x:A, (exists n : _, F x n) -> Acc inv_lt_rel x.
intros x [n fxn]; generalize x fxn; clear x fxn.
pattern n; apply (well_founded_induction_type lt_wf); intros.
constructor; intros.
inversion H0.
apply (H x1); auto.
Qed.

Theorem well_founded_inv_rel_compat : well_founded inv_lt_rel.
constructor; intros.
inversion H.
apply acc_lt_rel; trivial.
exists x; trivial.
Qed.

End LT_WF_REL.

Definition lex_nat := lex _ _ lt lt.

Lemma lex_nat_well_founded : well_founded lex_nat.
exact (lex_well_founded _ _ lt lt lt_wf lt_wf).
Qed.

Definition interp_mark_m  (e : var_type) (n:nat): Prop :=
exists lp : list pointer,
    reachable_elements e.(a) e.(l) e.(r) e.(p) e.(t) lp /\ 
  (mesure_mark e.(m) lp)=n.

Definition interp_mark_c  (e: var_type) (n:nat): Prop :=
exists lp : list pointer,
    reachable_elements e.(a) e.(l) e.(r) e.(p) e.(t) lp /\ 
   (mesure_mark e.(c) lp)=n.

Definition interp_pile (e : var_type) (n:nat) : Prop :=
exists pile : list pointer,
      clr_list e.(a) e.(c) e.(l) e.(r) e.(p) pile /\ 
       (List.length pile)=n.

Definition natnat := {x : nat & nat}.

Definition interp_mark_c_and_stack (e : var_type) (p: natnat) : Prop :=
  let (n,m) := p in
    interp_mark_c e n /\ interp_pile e m.

Definition order_mark_c_and_stack : var_type -> var_type -> Prop := 
  inv_lt_rel var_type natnat lex_nat interp_mark_c_and_stack.

Lemma order_mark_c_and_stack_wf : 
  well_founded order_mark_c_and_stack.
Proof.
unfold order_mark_c_and_stack.
apply well_founded_inv_rel_compat.
apply lex_nat_well_founded.
Qed.

Definition natnatnat := {x : nat & natnat}.

Definition interp_mark_m_and_c_and_stack (e : var_type) (t: natnatnat) : Prop :=
  let (n,p) := t in
    interp_mark_m e n /\ interp_mark_c_and_stack e p.

Definition lex_natnatnat := lex _ _ lt lex_nat.

Lemma lex_natnatnat_well_founded : well_founded lex_natnatnat.
exact (lex_well_founded _ _ lt lex_nat lt_wf lex_nat_well_founded).
Qed.

Definition order_mark_m_and_c_and_stack : var_type -> var_type -> Prop := 
  inv_lt_rel var_type natnatnat lex_natnatnat interp_mark_m_and_c_and_stack.


Lemma order_mark_m_and_c_and_stack_wf : 
  well_founded order_mark_m_and_c_and_stack.
Proof.
unfold order_mark_m_and_c_and_stack.
apply well_founded_inv_rel_compat.
apply lex_natnatnat_well_founded.
Qed.




