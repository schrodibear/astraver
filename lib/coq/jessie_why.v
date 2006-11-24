(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Why.

Set Implicit Arguments.

(*Why type*) Definition alloc_table: Set.
Admitted.

(*Why type*) Definition pointer: Set.
Admitted.

(*Why logic*) Definition offset_max : alloc_table -> pointer -> Z.
Admitted.

(*Why logic*) Definition offset_min : alloc_table -> pointer -> Z.
Admitted.

(*Why predicate*) Definition valid  (a:alloc_table) (p:pointer)
  := (offset_min a p) <= 0 /\ (offset_max a p) >= 0.

(*Why type*) Definition memory: Set ->Set.
Admitted.

(*Why logic*) Definition select :
  forall (A1:Set), ((memory) A1) -> pointer -> A1.
Admitted.

(*Why logic*) Definition store :
  forall (A1:Set), ((memory) A1) -> pointer -> A1 -> ((memory) A1).
Admitted.


(*Why axiom*) Lemma select_store_eq :
  forall (A1:Set),
  (forall (m:((memory) A1)),
   (forall (p1:pointer),
    (forall (p2:pointer),
     (forall (a:A1), (p1 = p2 -> (select (store m p1 a) p2) = a))))).
Admitted.

(*Why axiom*) Lemma select_store_neq :
  forall (A1:Set),
  (forall (m:((memory) A1)),
   (forall (p1:pointer),
    (forall (p2:pointer),
     (forall (a:A1),
      (~(p1 = p2) -> (select (store m p1 a) p2) = (select m p2)))))).
Admitted.

(*Why type*) Definition pset: Set.
Admitted.


(*Why logic*) Definition pset_empty : pset.
Admitted.

Set Contextual Implicit.
Implicit Arguments pset_empty.
Unset Contextual Implicit.

(*Why logic*) Definition pset_singleton : pointer -> pset.
Admitted.

(*Why logic*) Definition pset_union : pset -> pset -> pset.
Admitted.

(*Why logic*) Definition in_pset : pointer -> pset -> Prop.
Admitted.

(*Why axiom*) Lemma in_pset_empty :
  (forall (p:pointer), ~(in_pset p pset_empty)).
Admitted.

(*Why axiom*) Lemma in_pset_singleton :
  (forall (p:pointer),
   (forall (q:pointer), ((in_pset p (pset_singleton q)) <-> p = q))).
Admitted.

(*Why axiom*) Lemma in_pset_union :
  (forall (p:pointer),
   (forall (s1:pset),
    (forall (s2:pset),
     ((in_pset p (pset_union s1 s2)) <-> (in_pset p s1) \/ (in_pset p s2))))).
Admitted.


(*Why predicate*) Definition not_assigns (A94:Set) (a:alloc_table)
  (m1:((memory) A94)) (m2:((memory) A94)) (l:pset)
  := (forall (p:pointer),
      ((valid a p) /\ ~(in_pset p l) -> (select m2 p) = (select m1 p))).

(*Why type*) Definition struct_id: Set.
Admitted.

(*Why logic*) Definition instanceof :
  alloc_table -> pointer -> struct_id -> Prop.
Admitted.

(*Why logic*) Definition downcast :
  alloc_table -> pointer -> struct_id -> pointer.
Admitted.

(*Why axiom*) Lemma downcast_instanceof :
  (forall (a:alloc_table),
   (forall (p:pointer),
    (forall (s:struct_id), ((instanceof a p s) -> (downcast a p s) = p)))).
Admitted.

