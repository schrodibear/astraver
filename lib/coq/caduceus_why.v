(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Why.
Require Export WhyFloat.

Parameter pointer : Set.
Parameter alloc : Set.
Parameter memory : Set -> Set.
Parameter assign_loc : Set.

(*Why*) Parameter any_int : forall (_: unit), Z.

(*Why*) Parameter any_float : forall (_: unit), R.

(*Why*) Parameter any_pointer : forall (_: unit), pointer.

(*Why*) Parameter null : pointer.

(*Why logic*) Definition block_length : alloc -> pointer -> Z.
Admitted.

(*Why logic*) Definition offset : pointer -> Z.
Admitted.

(*Why logic*) Definition shift : pointer -> Z -> pointer.
Admitted.

(*Why*) Parameter eq_pointer :
  forall (p: pointer), forall (q: pointer),
  (sig_1 bool (fun (result: bool)  => ((if result then p = q else ~(p = q))))).

(*Why*) Parameter neq_pointer :
  forall (p: pointer), forall (q: pointer),
  (sig_1 bool (fun (result: bool)  => ((if result then ~(p = q) else p = q)))).

(*Why predicate*) Definition valid  (a:alloc) (p:pointer)
  := ~(p = null) /\ 0 <= (offset p) /\ (offset p) < (block_length a p).

(*Why predicate*) Definition valid_index  (a:alloc) (p:pointer) (i:Z)
  := ~(p = null) /\ 0 <= ((offset p) + i) /\ ((offset p) + i) <
     (block_length a p).

(*Why predicate*) Definition valid_range  (a:alloc) (p:pointer) (i:Z) (j:Z)
  := ~(p = null) /\ 0 <= ((offset p) + i) /\ i <= j /\ ((offset p) + j) <
     (block_length a p).

(*Why axiom*) Lemma offset_shift :
  (forall (p:pointer),
   (forall (i:Z), (offset (shift p i)) = ((offset p) + i))).
Admitted.

(*Why axiom*) Lemma block_length_shift :
  (forall (a:alloc),
   (forall (p:pointer),
    (forall (i:Z), (block_length a (shift p i)) = (block_length a p)))).
Admitted.

(*Why axiom*) Lemma shift_null :
  (forall (p:pointer), (forall (i:Z), (p = null -> (shift p i) = null))).
Admitted.

(*Why axiom*) Lemma shift_not_null :
  (forall (p:pointer), (forall (i:Z), (~(p = null) -> ~((shift p i) = null)))).
Admitted.

(*Why*) Parameter shift_ :
  forall (p: pointer), forall (i: Z),
  (sig_1 pointer (fun (result: pointer)  => (result = (shift p i)))).

(*Why logic*) Definition acc :
  forall (A27:Set), ((memory) A27) -> pointer -> A27.
Admitted.
Implicit Arguments acc.

(*Why*) Parameter acc_ :
  forall (A5: Set), forall (p: pointer), forall (alloc: alloc),
  forall (m: ((memory) A5)), forall (H: (valid alloc p)),
  (sig_1 A5 (fun (result: A5)  => (result = (acc m p)))).

(*Why logic*) Definition upd :
  forall (A28:Set), ((memory) A28) -> pointer -> A28 -> ((memory) A28).
Admitted.
Implicit Arguments upd.

(*Why*) Parameter upd_ :
  forall (A11: Set), forall (p: pointer), forall (v: A11),
  forall (alloc: alloc), forall (m: ((memory) A11)),
  forall (H: (valid alloc p)),
  (sig_2 ((memory) A11) unit
   (fun (m0: ((memory) A11)) (result: unit)  => (m0 = (upd m p v)))).

(*Why axiom*) Lemma acc_upd_eq :
  forall (A29:Set),
  (forall (m:((memory) A29)),
   (forall (p:pointer), (forall (a:A29), (acc (upd m p a) p) = a))).
Admitted.

(*Why axiom*) Lemma acc_upd_neq :
  forall (A30:Set),
  (forall (m:((memory) A30)),
   (forall (p1:pointer),
    (forall (p2:pointer),
     (forall (a:A30), (~(p1 = p2) -> (acc (upd m p1 a) p2) = (acc m p2)))))).
Admitted.

(*Why logic*) Definition fresh : alloc -> pointer -> Prop.
Admitted.

(*Why axiom*) Lemma false_not_true : ~(false = true).
Admitted.

(*Why logic*) Definition pointer_loc : pointer -> assign_loc.
Admitted.

(*Why logic*) Definition union_loc : assign_loc -> assign_loc -> assign_loc.
Admitted.

(*Why logic*) Definition unchanged : pointer -> assign_loc -> Prop.
Admitted.

(*Why predicate*) Definition assigns (A31:Set) (a:alloc) (m1:((memory) A31))
  (m2:((memory) A31)) (l:assign_loc)
  := (forall (p:pointer),
      ((valid a p) /\ (unchanged p l) -> (acc m2 p) = (acc m1 p))).
Implicit Arguments assigns.

(*Why axiom*) Lemma unchanged_pointer_elim :
  (forall (p1:pointer),
   (forall (p2:pointer), (~(p1 = p2) -> (unchanged p1 (pointer_loc p2))))).
Admitted.

(*Why axiom*) Lemma unchanged_pointer_intro :
  (forall (p1:pointer),
   (forall (p2:pointer), ((unchanged p1 (pointer_loc p2)) -> ~(p1 = p2)))).
Admitted.

(*Why axiom*) Lemma unchanged_union_elim :
  (forall (l1:assign_loc),
   (forall (l2:assign_loc),
    (forall (p:pointer),
     ((unchanged p l1) /\ (unchanged p l2) -> (unchanged p (union_loc l1 l2)))))).
Admitted.

(*Why axiom*) Lemma unchanged_union_intro1 :
  (forall (l1:assign_loc),
   (forall (l2:assign_loc),
    (forall (p:pointer),
     ((unchanged p (union_loc l1 l2)) -> (unchanged p l1))))).
Admitted.

(*Why axiom*) Lemma unchanged_union_intro2 :
  (forall (l1:assign_loc),
   (forall (l2:assign_loc),
    (forall (p:pointer),
     ((unchanged p (union_loc l1 l2)) -> (unchanged p l2))))).
Admitted.

