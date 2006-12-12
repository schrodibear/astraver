(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Why.

Set Implicit Arguments.

(*Why type*) Definition alloc_table: Set ->Set.
Admitted.

(*Why type*) Definition pointer: Set ->Set.
Admitted.

(*Why logic*) Definition offset_max :
  forall (A1:Set), ((alloc_table) A1) -> ((pointer) A1) -> Z.
Admitted.

(*Why logic*) Definition offset_min :
  forall (A1:Set), ((alloc_table) A1) -> ((pointer) A1) -> Z.
Admitted.

(*Why predicate*) Definition valid (A158:Set) (a:((alloc_table) A158))
  (p:((pointer) A158)) := (offset_min a p) <= 0 /\ (offset_max a p) >= 0.

(*Why logic*) Definition shift :
  forall (A1:Set), ((pointer) A1) -> Z -> ((pointer) A1).
Admitted.
Implicit Arguments shift.

(*Why axiom*) Lemma offset_max_shift :
  forall (A1:Set),
  (forall (a:((alloc_table) A1)),
   (forall (p:((pointer) A1)),
    (forall (i:Z), (offset_max a (shift p i)) = ((offset_max a p) - i)))).
Admitted.
Implicit Arguments offset_max_shift.

(*Why axiom*) Lemma offset_min_shift :
  forall (A1:Set),
  (forall (a:((alloc_table) A1)),
   (forall (p:((pointer) A1)),
    (forall (i:Z), (offset_min a (shift p i)) = ((offset_min a p) - i)))).
Admitted.
Implicit Arguments offset_min_shift.

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


(*Why predicate*) Definition not_assigns (A178:Set)
  (A177:Set) (a:((alloc_table) A177)) (m1:((memory) A177 A178))
  (m2:((memory) A177 A178)) (l:((pset) A177))
  := (forall (p:((pointer) A177)),
      ((valid a p) /\ ~(in_pset p l) -> (select m2 p) = (select m1 p))).


(*Why type*) Definition tag_table: Set ->Set.
Admitted.

(*Why type*) Definition tag_id: Set ->Set.
Admitted.

(*Why logic*) Definition instanceof :
  forall (A1:Set), ((tag_table) A1) -> ((pointer) A1)
  -> ((tag_id) A1) -> Prop.
Admitted.
Implicit Arguments instanceof.

(*Why logic*) Definition downcast :
  forall (A1:Set), ((tag_table) A1) -> ((pointer) A1)
  -> ((tag_id) A1) -> ((pointer) A1).
Admitted.
Implicit Arguments downcast.

(*Why axiom*) Lemma downcast_instanceof :
  forall (A1:Set),
  (forall (a:((tag_table) A1)),
   (forall (p:((pointer) A1)),
    (forall (s:((tag_id) A1)), ((instanceof a p s) -> (downcast a p s) = p)))).
Admitted.
Implicit Arguments downcast_instanceof.

