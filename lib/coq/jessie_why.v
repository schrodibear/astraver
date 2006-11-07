(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Why.

Set Implicit Arguments.

(*Why type*) Definition alloc_table: Set.
Admitted.

(*Why type*) Definition pointer: Set ->Set.
Admitted.

(*Why logic*) Definition offset_max :
  forall (A1:Set), alloc_table -> ((pointer) A1) -> Z.
Admitted.

(*Why logic*) Definition offset_min :
  forall (A1:Set), alloc_table -> ((pointer) A1) -> Z.
Admitted.

(*Why predicate*) Definition valid (A138:Set) (a:alloc_table)
  (p:((pointer) A138)) := (offset_min a p) <= 0 /\ (offset_max a p) >= 0.

(*Why type*) Definition memory: Set -> Set ->Set.
Admitted.

(*Why logic*) Definition select :
  forall (A1:Set), forall (A2:Set), ((memory) A2 A1) -> ((pointer) A2) -> A1.
Admitted.

(*Why logic*) Definition store :
  forall (A1:Set), forall (A2:Set), ((memory) A1 A2) -> ((pointer) A1)
  -> A2 -> ((memory) A1 A2).
Admitted.


(*Why axiom*) Lemma select_store_eq :
  forall (A1:Set), forall (A2:Set),
  (forall (m:((memory) A1 A2)),
   (forall (p1:((pointer) A1)),
    (forall (p2:((pointer) A1)),
     (forall (a:A2), (p1 = p2 -> (select (store m p1 a) p2) = a))))).
Admitted.

(*Why axiom*) Lemma select_store_neq :
  forall (A1:Set), forall (A2:Set),
  (forall (m:((memory) A1 A2)),
   (forall (p1:((pointer) A1)),
    (forall (p2:((pointer) A1)),
     (forall (a:A2),
      (~(p1 = p2) -> (select (store m p1 a) p2) = (select m p2)))))).
Admitted.

(*Why type*) Definition pset: Set ->Set.
Admitted.


(*Why logic*) Definition pset_empty : forall (A1:Set), ((pset) A1).
Admitted.

Set Contextual Implicit.
Implicit Arguments pset_empty.
Unset Contextual Implicit.

(*Why logic*) Definition pset_singleton :
  forall (A1:Set), ((pointer) A1) -> ((pset) A1).
Admitted.

(*Why logic*) Definition pset_union :
  forall (A1:Set), ((pset) A1) -> ((pset) A1) -> ((pset) A1).
Admitted.

(*Why logic*) Definition in_pset :
  forall (A1:Set), ((pointer) A1) -> ((pset) A1) -> Prop.
Admitted.

(*Why axiom*) Lemma in_pset_empty :
  forall (A1:Set), (forall (p:((pointer) A1)), ~(in_pset p pset_empty)).
Admitted.

(*Why axiom*) Lemma in_pset_singleton :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (q:((pointer) A1)), ((in_pset p (pset_singleton q)) <-> p = q))).
Admitted.

(*Why axiom*) Lemma in_pset_union :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (s1:((pset) A1)),
    (forall (s2:((pset) A1)),
     ((in_pset p (pset_union s1 s2)) <-> (in_pset p s1) \/ (in_pset p s2))))).
Admitted.


(*Why predicate*) Definition not_assigns (A155:Set)
  (A154:Set) (a:alloc_table) (m1:((memory) A155 A154)) (m2:((memory) A155
  A154)) (l:((pset) A155))
  := (forall (p:((pointer) A155)),
      ((valid a p) /\ ~(in_pset p l) -> (select m2 p) = (select m1 p))).

