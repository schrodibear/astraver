(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require WhyFloat.

Parameter addr : Set.
Parameter pointer : Set.
Parameter alloc : Set.
Parameter memory : Set -> Set.
Parameter assign_loc : Set.

(*Why logic*) Definition bw_compl : Z -> Z.
Admitted.

(*Why logic*) Definition bw_and : Z -> Z -> Z.
Admitted.

(*Why logic*) Definition bw_xor : Z -> Z -> Z.
Admitted.

(*Why logic*) Definition bw_or : Z -> Z -> Z.
Admitted.

(*Why logic*) Definition lsl : Z -> Z -> Z.
Admitted.

(*Why logic*) Definition lsr : Z -> Z -> Z.
Admitted.

(*Why*) Parameter any_int : (_: unit)Z.

(*Why*) Parameter any_float : (_: unit)R.

(*Why*) Parameter any_pointer : (_: unit)pointer.

(*Why*) Parameter null : pointer.

(*Why logic*) Definition block_length : alloc_table -> pointer -> Z.
Admitted.

(*Why logic*) Definition base_addr : pointer -> addr.
Admitted.

(*Why logic*) Definition offset : pointer -> Z.
Admitted.

(*Why logic*) Definition shift : pointer -> Z -> pointer.
Admitted.

Admitted.

(*Why logic*) Definition sub_pointer : pointer -> pointer -> Z.
Admitted.

(*Why predicate*) Definition lt_pointer  [p1:pointer] [p2:pointer]
  := (base_addr p1) = (base_addr p2) /\ `(offset p1) < (offset p2)`.

(*Why predicate*) Definition le_pointer  [p1:pointer] [p2:pointer]
  := (base_addr p1) = (base_addr p2) /\ `(offset p1) <= (offset p2)`.

(*Why predicate*) Definition gt_pointer  [p1:pointer] [p2:pointer]
  := (base_addr p1) = (base_addr p2) /\ `(offset p1) > (offset p2)`.

(*Why predicate*) Definition ge_pointer  [p1:pointer] [p2:pointer]
  := (base_addr p1) = (base_addr p2) /\ `(offset p1) >= (offset p2)`.

(*Why*) Parameter eq_pointer :
  (p: pointer)(q: pointer)
  (sig_1 bool [result: bool]((if result then p = q else ~(p = q)))).

(*Why*) Parameter neq_pointer :
  (p: pointer)(q: pointer)
  (sig_1 bool [result: bool]((if result then ~(p = q) else p = q))).

(*Why predicate*) Definition valid  [a:alloc_table] [p:pointer]
  := ~(p = null) /\ `0 <= (offset p)` /\ `(offset p) < (block_length a p)`.

(*Why predicate*) Definition valid_index  [a:alloc_table] [p:pointer] [i:Z]
  := ~(p = null) /\ `0 <= (offset p) + i` /\
     `(offset p) + i < (block_length a p)`.

(*Why predicate*) Definition valid_range  [a:alloc_table] [p:pointer] [i:Z]
  [j:Z]
  := ~(p = null) /\ `0 <= (offset p) + i` /\ `i <= j` /\
     `(offset p) + j < (block_length a p)`.

Admitted.

(*Why axiom*) Lemma base_addr_shift :
  ((p:pointer) ((i:Z) (base_addr (shift p i)) = (base_addr p))).
Admitted.

(*Why axiom*) Lemma block_length_shift :
  ((a:alloc_table)
   ((p:pointer) ((i:Z) `(block_length a (shift p i)) = (block_length a p)`))).
Admitted.

(*Why axiom*) Lemma shift_null :
  ((p:pointer) ((i:Z) (p = null -> (shift p i) = null))).
Admitted.

(*Why axiom*) Lemma shift_not_null :
  ((p:pointer) ((i:Z) (~(p = null) -> ~((shift p i) = null)))).
Admitted.

(*Why axiom*) Lemma base_addr_block_length :
  ((a:alloc_table)
   ((p1:pointer)
    ((p2:pointer)
     ((base_addr p1) = (base_addr p2) ->
      `(block_length a p1) = (block_length a p2)`)))).
Admitted.

(*Why axiom*) Lemma pointer_pair_1 :
  ((p1:pointer)
   ((p2:pointer)
    ((base_addr p1) = (base_addr p2) /\ `(offset p1) = (offset p2)` ->
     p1 = p2))).
Admitted.

(*Why axiom*) Lemma pointer_pair_2 :
  ((p1:pointer)
   ((p2:pointer)
    (p1 = p2 -> (base_addr p1) = (base_addr p2) /\
     `(offset p1) = (offset p2)`))).
Admitted.

(*Why axiom*) Lemma neq_base_addr_neq_shift :
  ((p1:pointer)
   ((p2:pointer)
    ((i:Z)
     ((j:Z)
      (~((base_addr p1) = (base_addr p2)) -> ~((shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma neq_offset_neq_shift :
  ((p1:pointer)
   ((p2:pointer)
    ((i:Z)
     ((j:Z)
      (`(offset p1) + i <> (offset p2) + j` -> ~((shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma eq_offset_eq_shift :
  ((p1:pointer)
   ((p2:pointer)
    ((i:Z)
     ((j:Z)
      ((base_addr p1) = (base_addr p2) ->
       (`(offset p1) + i = (offset p2) + j` -> (shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma valid_index_valid_shift :
  ((a:alloc_table)
   ((p:pointer) ((i:Z) ((valid_index a p i) -> (valid a (shift p i)))))).
Admitted.

Admitted.

Admitted.

(*Why axiom*) Lemma valid_range_valid_shift :
  ((a:alloc_table)
   ((p:pointer)
    ((i:Z)
     ((j:Z)
      ((k:Z)
       ((valid_range a p i j) ->
        (`i <= k` /\ `k <= j` -> (valid a (shift p k))))))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid_index :
  ((a:alloc_table)
   ((p:pointer)
    ((i:Z)
     ((j:Z)
      ((k:Z)
       ((valid_range a p i j) ->
        (`i <= k` /\ `k <= j` -> (valid_index a p k)))))))).
Admitted.

(*Why axiom*) Lemma sub_pointer_def :
  ((p1:pointer)
   ((p2:pointer)
    ((base_addr p1) = (base_addr p2) ->
     `(sub_pointer p1 p2) = (offset p1) - (offset p2)`))).
Admitted.

(*Why*) Parameter shift_ :
  (p: pointer)(i: Z)(sig_1 pointer [result: pointer](result = (shift p i))).

(*Why*) Parameter sub_pointer_ :
  (p1: pointer)(p2: pointer)(H: (base_addr p1) = (base_addr p2))
  (sig_1 Z [result: Z](`result = (offset p1) - (offset p2)`)).

(*Why*) Parameter lt_pointer_ :
  (p1: pointer)(p2: pointer)(H: (base_addr p1) = (base_addr p2))
  (sig_1 bool [result: bool]
   ((if result then `(offset p1) < (offset p2)`
     else `(offset p1) >= (offset p2)`))).

(*Why*) Parameter le_pointer_ :
  (p1: pointer)(p2: pointer)(H: (base_addr p1) = (base_addr p2))
  (sig_1 bool [result: bool]
   ((if result then `(offset p1) <= (offset p2)`
     else `(offset p1) > (offset p2)`))).

(*Why*) Parameter gt_pointer_ :
  (p1: pointer)(p2: pointer)(H: (base_addr p1) = (base_addr p2))
  (sig_1 bool [result: bool]
   ((if result then `(offset p1) > (offset p2)`
     else `(offset p1) <= (offset p2)`))).

(*Why*) Parameter ge_pointer_ :
  (p1: pointer)(p2: pointer)(H: (base_addr p1) = (base_addr p2))
  (sig_1 bool [result: bool]
   ((if result then `(offset p1) >= (offset p2)`
     else `(offset p1) < (offset p2)`))).

(*Why logic*) Definition acc : (A41:Set) ((memory) A41) -> pointer -> A41.
Admitted.
Implicits acc [1].

(*Why*) Parameter acc_ :
  (A5: Set)(p: pointer)(alloc: alloc_table)(m: ((memory) A5))
  (H: (valid alloc p))(sig_1 A5 [result: A5](result = (acc m p))).

(*Why logic*) Definition upd :
  (A42:Set) ((memory) A42) -> pointer -> A42 -> ((memory) A42).
Admitted.
Implicits upd [1].

(*Why*) Parameter upd_ :
  (A11: Set)(p: pointer)(v: A11)(alloc: alloc_table)(m: ((memory) A11))
  (H: (valid alloc p))
  (sig_2 ((memory) A11) unit [m0: ((memory) A11)][result: unit]
   (m0 = (upd m p v))).

(*Why axiom*) Lemma acc_upd :
  (A43:Set)
  ((m:((memory) A43)) ((p:pointer) ((a:A43) (acc (upd m p a) p) = a))).
Admitted.

(*Why axiom*) Lemma acc_upd_eq :
  (A44:Set)
  ((m:((memory) A44))
   ((p1:pointer)
    ((p2:pointer) ((a:A44) (p1 = p2 -> (acc (upd m p1 a) p2) = a))))).
Admitted.

(*Why axiom*) Lemma acc_upd_neq :
  (A45:Set)
  ((m:((memory) A45))
   ((p1:pointer)
    ((p2:pointer)
     ((a:A45) (~(p1 = p2) -> (acc (upd m p1 a) p2) = (acc m p2)))))).
Admitted.

(*Why logic*) Definition fresh : alloc_table -> pointer -> Prop.
Admitted.

(*Why axiom*) Lemma false_not_true : ~(false = true).
Admitted.

(*Why logic*) Definition nothing_loc : assign_loc.
Admitted.

(*Why logic*) Definition pointer_loc : pointer -> assign_loc.
Admitted.

(*Why logic*) Definition all_loc : pointer -> assign_loc.
Admitted.

(*Why logic*) Definition range_loc : pointer -> Z -> Z -> assign_loc.
Admitted.

(*Why logic*) Definition union_loc : assign_loc -> assign_loc -> assign_loc.
Admitted.


(*Why logic*) Definition unchanged : pointer -> assign_loc -> Prop.
Admitted.

(*Why predicate*) Definition assigns [A46:Set] [a:alloc_table]
  [m1:((memory) A46)] [m2:((memory) A46)] [l:assign_loc]
  := ((p:pointer)
      ((valid a p) -> ((unchanged p l) -> (acc m2 p) = (acc m1 p)))).
Implicits assigns [1].

(*Why axiom*) Lemma unchanged_nothing_intro :
  ((p:pointer) (unchanged p nothing_loc)).
Admitted.

(*Why axiom*) Lemma unchanged_pointer_intro :
  ((p1:pointer)
   ((p2:pointer) (~(p1 = p2) -> (unchanged p1 (pointer_loc p2))))).
Admitted.

(*Why axiom*) Lemma unchanged_pointer_elim :
  ((p1:pointer)
   ((p2:pointer) ((unchanged p1 (pointer_loc p2)) -> ~(p1 = p2)))).
Admitted.

(*Why axiom*) Lemma unchanged_union_intro :
  ((l1:assign_loc)
   ((l2:assign_loc)
    ((p:pointer)
     ((unchanged p l1) /\ (unchanged p l2) -> (unchanged p (union_loc l1 l2)))))).
Admitted.

(*Why axiom*) Lemma unchanged_union_elim1 :
  ((l1:assign_loc)
   ((l2:assign_loc)
    ((p:pointer) ((unchanged p (union_loc l1 l2)) -> (unchanged p l1))))).
Admitted.

(*Why axiom*) Lemma unchanged_union_elim2 :
  ((l1:assign_loc)
   ((l2:assign_loc)
    ((p:pointer) ((unchanged p (union_loc l1 l2)) -> (unchanged p l2))))).
Admitted.

(*Why axiom*) Lemma unchanged_range_intro :
  ((p1:pointer)
   ((p2:pointer)
    ((a:Z)
     ((b:Z)
      (((i:Z) (`a <= i` /\ `i <= b` -> ~(p1 = (shift p2 i)))) ->
       (unchanged p1 (range_loc p2 a b))))))).
Admitted.

(*Why axiom*) Lemma unchanged_range_elim :
  ((p1:pointer)
   ((p2:pointer)
    ((a:Z)
     ((b:Z)
      ((unchanged p1 (range_loc p2 a b)) ->
       ((i:Z) (`a <= i` /\ `i <= b` -> ~(p1 = (shift p2 i))))))))).
Admitted.

Admitted.



Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

(*Why axiom*) Lemma assigns_trans :
  (A47:Set)
  ((a:alloc_table)
   ((l:assign_loc)
    ((m1:((memory) A47))
     ((m2:((memory) A47))
      ((m3:((memory) A47))
       ((assigns a m1 m2 l) -> ((assigns a m2 m3 l) -> (assigns a m1 m3 l)))))))).
Admitted.

