(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

Parameter pointer : Set.
Parameter alloc : Set.
Parameter memory : Set -> Set.

(*Why*) Parameter any_int : (_: unit)Z.

(*Why*) Parameter any_pointer : (_: unit)pointer.

(*Why logic*) Definition null : pointer.
Admitted.

(*Why logic*) Definition block_length : alloc -> pointer -> Z.
Admitted.

(*Why logic*) Definition offset : pointer -> Z.
Admitted.

(*Why logic*) Definition shift : pointer -> Z -> pointer.
Admitted.

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

(*Why logic*) Definition acc : (A23:Set) ((memory) A23) -> pointer -> A23.
Admitted.
Implicits acc [1].

(*Why*) Parameter acc_ :
  (A5: Set)(p: pointer)(alloc: alloc)(m: ((memory) A5))(H: (valid alloc p))
  (sig_1 A5 [result: A5](result = (acc m p))).

(*Why logic*) Definition upd :
  (A24:Set) ((memory) A24) -> pointer -> A24 -> ((memory) A24).
Admitted.
Implicits upd [1].

(*Why*) Parameter upd_ :
  (A11: Set)(p: pointer)(v: A11)(alloc: alloc)(m: ((memory) A11))
  (H: (valid alloc p))
  (sig_2 ((memory) A11) unit [m0: ((memory) A11)][result: unit]
   (m0 = (upd m p v))).

(*Why axiom*) Lemma acc_upd_eq :
  (A25:Set)
  ((m:((memory) A25)) ((p:pointer) ((a:A25) (acc (upd m p a) p) = a))).
Admitted.

(*Why axiom*) Lemma acc_upd_neq :
  (A26:Set)
  ((m:((memory) A26))
   ((p1:pointer)
    ((p2:pointer)
     ((a:A26) (~(p1 = p2) -> (acc (upd m p1 a) p2) = (acc m p2)))))).
Admitted.

(*Why logic*) Definition fresh : alloc -> pointer -> Prop.
Admitted.

(*Why axiom*) Lemma false_not_true : ~(false = true).
Admitted.

