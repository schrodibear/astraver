(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require WhyFloat.

Parameter pointer : Set.
Parameter alloc : Set.
Parameter memory : Set -> Set.
Parameter assign_loc : Set.

(*Why*) Parameter any_int : (_: unit)Z.

(*Why*) Parameter any_float : (_: unit)R.

(*Why*) Parameter any_pointer : (_: unit)pointer.

(*Why*) Parameter null : pointer.

(*Why logic*) Definition block_length : alloc -> pointer -> Z.
Admitted.

(*Why logic*) Definition offset : pointer -> Z.
Admitted.

(*Why logic*) Definition shift : pointer -> Z -> pointer.
Admitted.

(*Why*) Parameter eq_pointer :
  (p: pointer)(q: pointer)
  (sig_1 bool [result: bool]((if result then p = q else ~(p = q)))).

(*Why*) Parameter neq_pointer :
  (p: pointer)(q: pointer)
  (sig_1 bool [result: bool]((if result then ~(p = q) else p = q))).

(*Why predicate*) Definition valid  [a:alloc] [p:pointer]
  := ~(p = null) /\ `0 <= (offset p)` /\ `(offset p) < (block_length a p)`.

(*Why predicate*) Definition valid_index  [a:alloc] [p:pointer] [i:Z]
  := ~(p = null) /\ `0 <= (offset p) + i` /\
     `(offset p) + i < (block_length a p)`.

(*Why predicate*) Definition valid_range  [a:alloc] [p:pointer] [i:Z] [j:Z]
  := ~(p = null) /\ `0 <= (offset p) + i` /\ `i <= j` /\
     `(offset p) + j < (block_length a p)`.

(*Why axiom*) Lemma offset_shift :
  ((p:pointer) ((i:Z) `(offset (shift p i)) = (offset p) + i`)).
Admitted.

(*Why axiom*) Lemma block_length_shift :
  ((a:alloc)
   ((p:pointer) ((i:Z) `(block_length a (shift p i)) = (block_length a p)`))).
Admitted.

(*Why axiom*) Lemma shift_null :
  ((p:pointer) ((i:Z) (p = null -> (shift p i) = null))).
Admitted.

(*Why axiom*) Lemma shift_not_null :
  ((p:pointer) ((i:Z) (~(p = null) -> ~((shift p i) = null)))).
Admitted.

(*Why*) Parameter shift_ :
  (p: pointer)(i: Z)(sig_1 pointer [result: pointer](result = (shift p i))).

(*Why logic*) Definition acc : (A27:Set) ((memory) A27) -> pointer -> A27.
Admitted.
Implicits acc [1].

(*Why*) Parameter acc_ :
  (A5: Set)(p: pointer)(alloc: alloc)(m: ((memory) A5))(H: (valid alloc p))
  (sig_1 A5 [result: A5](result = (acc m p))).

(*Why logic*) Definition upd :
  (A28:Set) ((memory) A28) -> pointer -> A28 -> ((memory) A28).
Admitted.
Implicits upd [1].

(*Why*) Parameter upd_ :
  (A11: Set)(p: pointer)(v: A11)(alloc: alloc)(m: ((memory) A11))
  (H: (valid alloc p))
  (sig_2 ((memory) A11) unit [m0: ((memory) A11)][result: unit]
   (m0 = (upd m p v))).

(*Why axiom*) Lemma acc_upd_eq :
  (A29:Set)
  ((m:((memory) A29)) ((p:pointer) ((a:A29) (acc (upd m p a) p) = a))).
Admitted.

(*Why axiom*) Lemma acc_upd_neq :
  (A30:Set)
  ((m:((memory) A30))
   ((p1:pointer)
    ((p2:pointer)
     ((a:A30) (~(p1 = p2) -> (acc (upd m p1 a) p2) = (acc m p2)))))).
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

(*Why predicate*) Definition assigns [A31:Set] [a:alloc] [m1:((memory) A31)]
  [m2:((memory) A31)] [l:assign_loc]
  := ((p:pointer)
      (~(fresh a p) /\ (unchanged p l) -> (acc m1 p) = (acc m2 p))).
Implicits assigns [1].

(*Why axiom*) Lemma unchanged_pointer1 :
  ((p1:pointer)
   ((p2:pointer) ((unchanged p1 (pointer_loc p2)) -> ~(p1 = p2)))).
Admitted.

(*Why axiom*) Lemma unchanged_pointer2 :
  ((p1:pointer)
   ((p2:pointer) (~(p1 = p2) -> (unchanged p1 (pointer_loc p2))))).
Admitted.

(*Why axiom*) Lemma unchanged_union1 :
  ((l1:assign_loc)
   ((l2:assign_loc)
    ((p:pointer)
     ((unchanged p (union_loc l1 l2)) -> (unchanged p l1) /\ (unchanged p l2))))).
Admitted.

(*Why axiom*) Lemma unchanged_union2 :
  ((l1:assign_loc)
   ((l2:assign_loc)
    ((p:pointer)
     ((unchanged p l1) /\ (unchanged p l2) -> (unchanged p (union_loc l1 l2)))))).
Admitted.

