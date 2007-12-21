(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require WhyReal.

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





(*Why logic*) Definition non_int : Z -> Z.
Admitted.

(*Why type*) Definition pointer: Set ->Set.

























































Admitted.

(*Why type*) Definition addr: Set ->Set.
Admitted.

(*Why type*) Definition alloc_table: Set.
Admitted.






(*Why logic*) Definition block_length :
  (A1:Set) alloc_table -> (pointer A1) -> Z.
Admitted.
Implicit Arguments block_length.

(*Why logic*) Definition base_addr : (A1:Set) (pointer A1) -> (addr A1).
Admitted.
Implicit Arguments base_addr.

(*Why logic*) Definition offset : (A1:Set) (pointer A1) -> Z.
Admitted.
Implicit Arguments offset.

(*Why logic*) Definition shift : (A1:Set) (pointer A1) -> Z -> (pointer A1).
Admitted.
Implicit Arguments shift.

(*Why logic*) Definition sub_pointer :
  (A1:Set) (pointer A1) -> (pointer A1) -> Z.
Admitted.
Implicit Arguments sub_pointer.

(*Why predicate*) Definition lt_pointer [A682:Set] [p1:(pointer A682)] [p2:(pointer A682)]
  := (base_addr p1) = (base_addr p2) /\ `(offset p1) < (offset p2)`.
Implicit Arguments lt_pointer.

(*Why predicate*) Definition le_pointer [A683:Set] [p1:(pointer A683)] [p2:(pointer A683)]
  := (base_addr p1) = (base_addr p2) /\ `(offset p1) <= (offset p2)`.
Implicit Arguments le_pointer.

(*Why predicate*) Definition gt_pointer [A684:Set] [p1:(pointer A684)] [p2:(pointer A684)]
  := (base_addr p1) = (base_addr p2) /\ `(offset p1) > (offset p2)`.
Implicit Arguments gt_pointer.

(*Why predicate*) Definition ge_pointer [A685:Set] [p1:(pointer A685)] [p2:(pointer A685)]
  := (base_addr p1) = (base_addr p2) /\ `(offset p1) >= (offset p2)`.
Implicit Arguments ge_pointer.

(*Why predicate*) Definition valid [A686:Set] [a:alloc_table] [p:(pointer A686)]
  := `0 <= (offset p)` /\ `(offset p) < (block_length a p)`.
Implicit Arguments valid.

(*Why predicate*) Definition valid_index [A687:Set] [a:alloc_table] [p:(pointer A687)] [i:Z]
  := `0 <= (offset p) + i` /\ `(offset p) + i < (block_length a p)`.
Implicit Arguments valid_index.

(*Why predicate*) Definition valid_range [A688:Set] [a:alloc_table] [p:(pointer A688)] [i:Z] [j:Z]
  := `0 <= (offset p) + i` /\ `(offset p) + j < (block_length a p)`.
Implicit Arguments valid_range.

(*Why axiom*) Lemma offset_shift :
  (A1:Set) ((p:(pointer A1)) ((i:Z) `(offset (shift p i)) = (offset p) + i`)).
Admitted.

(*Why axiom*) Lemma shift_zero :
  (A1:Set) ((p:(pointer A1)) (shift p `0`) = p).
Admitted.

(*Why axiom*) Lemma shift_shift :
  (A1:Set)
  ((p:(pointer A1)) ((i:Z) ((j:Z) (shift (shift p i) j) = (shift p `i + j`)))).
Admitted.

(*Why axiom*) Lemma base_addr_shift :
  (A1:Set) ((p:(pointer A1)) ((i:Z) (base_addr (shift p i)) = (base_addr p))).
Admitted.

(*Why axiom*) Lemma block_length_shift :
  (A1:Set)
  ((a:alloc_table)
   ((p:(pointer A1))
    ((i:Z) `(block_length a (shift p i)) = (block_length a p)`))).
Admitted.

(*Why axiom*) Lemma base_addr_block_length :
  (A1:Set)
  ((a:alloc_table)
   ((p1:(pointer A1))
    ((p2:(pointer A1))
     ((base_addr p1) = (base_addr p2) ->
      `(block_length a p1) = (block_length a p2)`)))).
Admitted.

(*Why axiom*) Lemma pointer_pair_1 :
  (A1:Set)
  ((p1:(pointer A1))
   ((p2:(pointer A1))
    ((base_addr p1) = (base_addr p2) /\ `(offset p1) = (offset p2)` ->
     p1 = p2))).
Admitted.

(*Why axiom*) Lemma pointer_pair_2 :
  (A1:Set)
  ((p1:(pointer A1))
   ((p2:(pointer A1))
    (p1 = p2 -> (base_addr p1) = (base_addr p2) /\
     `(offset p1) = (offset p2)`))).
Admitted.

(*Why axiom*) Lemma neq_base_addr_neq_shift :
  (A1:Set)
  ((p1:(pointer A1))
   ((p2:(pointer A1))
    ((i:Z)
     ((j:Z)
      (~((base_addr p1) = (base_addr p2)) -> ~((shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma neq_offset_neq_shift :
  (A1:Set)
  ((p1:(pointer A1))
   ((p2:(pointer A1))
    ((i:Z)
     ((j:Z)
      (`(offset p1) + i <> (offset p2) + j` -> ~((shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma eq_offset_eq_shift :
  (A1:Set)
  ((p1:(pointer A1))
   ((p2:(pointer A1))
    ((i:Z)
     ((j:Z)
      ((base_addr p1) = (base_addr p2) ->
       (`(offset p1) + i = (offset p2) + j` -> (shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma valid_index_valid_shift :
  (A1:Set)
  ((a:alloc_table)
   ((p:(pointer A1)) ((i:Z) ((valid_index a p i) -> (valid a (shift p i)))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid_shift :
  (A1:Set)
  ((a:alloc_table)
   ((p:(pointer A1))
    ((i:Z)
     ((j:Z)
      ((k:Z)
       ((valid_range a p i j) ->
        (`i <= k` /\ `k <= j` -> (valid a (shift p k))))))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid :
  (A1:Set)
  ((a:alloc_table)
   ((p:(pointer A1))
    ((i:Z)
     ((j:Z) ((valid_range a p i j) -> (`i <= 0` /\ `0 <= j` -> (valid a p))))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid_index :
  (A1:Set)
  ((a:alloc_table)
   ((p:(pointer A1))
    ((i:Z)
     ((j:Z)
      ((k:Z)
       ((valid_range a p i j) ->
        (`i <= k` /\ `k <= j` -> (valid_index a p k)))))))).
Admitted.

(*Why axiom*) Lemma sub_pointer_def :
  (A1:Set)
  ((p1:(pointer A1))
   ((p2:(pointer A1))
    ((base_addr p1) = (base_addr p2) ->
     `(sub_pointer p1 p2) = (offset p1) - (offset p2)`))).
Admitted.

(*Why type*) Definition memory: Set -> Set ->Set.
Admitted.

(*Why logic*) Definition acc :
  (A1:Set) (A2:Set) (memory A1 A2) -> (pointer A2) -> A1.
Admitted.
Implicit Arguments acc.

(*Why logic*) Definition upd :
  (A1:Set) (A2:Set) (memory A1 A2) -> (pointer A2) -> A1 -> (memory A1 A2).
Admitted.
Implicit Arguments upd.

(*Why axiom*) Lemma acc_upd :
  (A1:Set) (A2:Set)
  ((m:(memory A1 A2)) ((p:(pointer A2)) ((a:A1) (acc (upd m p a) p) = a))).
Admitted.

(*Why axiom*) Lemma acc_upd_neq :
  (A1:Set) (A2:Set)
  ((m:(memory A1 A2))
   ((p1:(pointer A2))
    ((p2:(pointer A2))
     ((a:A1) (~(p1 = p2) -> (acc (upd m p1 a) p2) = (acc m p2)))))).
Admitted.

(*Why axiom*) Lemma false_not_true : ~(false = true).
Admitted.

(*Why type*) Definition pset: Set ->Set.
Admitted.

(*Why logic*) Definition pset_empty : (A1:Set) (pset A1).
Admitted.
Set Contextual Implicit.
Implicit Arguments pset_empty.
Unset Contextual Implicit.

(*Why logic*) Definition pset_singleton : (A1:Set) (pointer A1) -> (pset A1).
Admitted.
Implicit Arguments pset_singleton.

(*Why logic*) Definition pset_star :
  (A1:Set) (A2:Set) (pset A2) -> (memory (pointer A1) A2) -> (pset A1).
Admitted.
Implicit Arguments pset_star.

(*Why logic*) Definition pset_all : (A1:Set) (pset A1) -> (pset A1).
Admitted.
Implicit Arguments pset_all.

(*Why logic*) Definition pset_range :
  (A1:Set) (pset A1) -> Z -> Z -> (pset A1).
Admitted.
Implicit Arguments pset_range.

(*Why logic*) Definition pset_range_left :
  (A1:Set) (pset A1) -> Z -> (pset A1).
Admitted.
Implicit Arguments pset_range_left.

(*Why logic*) Definition pset_range_right :
  (A1:Set) (pset A1) -> Z -> (pset A1).
Admitted.
Implicit Arguments pset_range_right.

(*Why logic*) Definition pset_acc_all :
  (A1:Set) (A2:Set) (pset A2) -> (memory (pointer A1) A2) -> (pset A1).
Admitted.
Implicit Arguments pset_acc_all.

(*Why logic*) Definition pset_acc_range :
  (A1:Set) (A2:Set) (pset A2) -> (memory (pointer A1) A2) -> Z
  -> Z -> (pset A1).
Admitted.
Implicit Arguments pset_acc_range.

(*Why logic*) Definition pset_acc_range_left :
  (A1:Set) (A2:Set) (pset A2) -> (memory (pointer A1) A2) -> Z -> (pset A1).
Admitted.
Implicit Arguments pset_acc_range_left.

(*Why logic*) Definition pset_acc_range_right :
  (A1:Set) (A2:Set) (pset A2) -> (memory (pointer A1) A2) -> Z -> (pset A1).
Admitted.
Implicit Arguments pset_acc_range_right.

(*Why logic*) Definition pset_union :
  (A1:Set) (pset A1) -> (pset A1) -> (pset A1).
Admitted.
Implicit Arguments pset_union.

(*Why logic*) Definition not_in_pset :
  (A1:Set) (pointer A1) -> (pset A1) -> Prop.
Admitted.
Implicit Arguments not_in_pset.

(*Why predicate*) Definition not_assigns [A732:Set] [A731:Set] [a:alloc_table] [m1:(memory A731 A732)] [m2:(memory A731 A732)] [l:(pset A732)]
  := ((p:(pointer A732))
      ((valid a p) -> ((not_in_pset p l) -> (acc m2 p) = (acc m1 p)))).
Implicit Arguments not_assigns.

(*Why axiom*) Lemma pset_empty_intro :
  (A1:Set) ((p:(pointer A1)) (not_in_pset p (@pset_empty A1))).
Admitted.

(*Why axiom*) Lemma pset_singleton_intro :
  (A1:Set)
  ((p1:(pointer A1))
   ((p2:(pointer A1)) (~(p1 = p2) -> (not_in_pset p1 (pset_singleton p2))))).
Admitted.

(*Why axiom*) Lemma pset_singleton_elim :
  (A1:Set)
  ((p1:(pointer A1))
   ((p2:(pointer A1)) ((not_in_pset p1 (pset_singleton p2)) -> ~(p1 = p2)))).
Admitted.

(*Why axiom*) Lemma not_not_in_singleton :
  (A1:Set) ((p:(pointer A1)) ~(not_in_pset p (pset_singleton p))).
Admitted.

(*Why axiom*) Lemma pset_union_intro :
  (A1:Set)
  ((l1:(pset A1))
   ((l2:(pset A1))
    ((p:(pointer A1))
     ((not_in_pset p l1) /\ (not_in_pset p l2) ->
      (not_in_pset p (pset_union l1 l2)))))).
Admitted.

(*Why axiom*) Lemma pset_union_elim1 :
  (A1:Set)
  ((l1:(pset A1))
   ((l2:(pset A1))
    ((p:(pointer A1))
     ((not_in_pset p (pset_union l1 l2)) -> (not_in_pset p l1))))).
Admitted.

(*Why axiom*) Lemma pset_union_elim2 :
  (A1:Set)
  ((l1:(pset A1))
   ((l2:(pset A1))
    ((p:(pointer A1))
     ((not_in_pset p (pset_union l1 l2)) -> (not_in_pset p l2))))).
Admitted.

(*Why axiom*) Lemma pset_star_intro :
  (A1:Set) (A2:Set)
  ((l:(pset A1))
   ((m:(memory (pointer A2) A1))
    ((p:(pointer A2))
     (((p1:(pointer A1)) (p = (acc m p1) -> (not_in_pset p1 l))) ->
      (not_in_pset p (pset_star l m)))))).
Admitted.

(*Why axiom*) Lemma pset_star_elim :
  (A1:Set) (A2:Set)
  ((l:(pset A1))
   ((m:(memory (pointer A2) A1))
    ((p:(pointer A2))
     ((not_in_pset p (pset_star l m)) ->
      ((p1:(pointer A1)) (p = (acc m p1) -> (not_in_pset p1 l))))))).
Admitted.

(*Why axiom*) Lemma pset_all_intro :
  (A1:Set)
  ((p:(pointer A1))
   ((l:(pset A1))
    (((p1:(pointer A1))
      (~(not_in_pset p1 l) -> ~((base_addr p) = (base_addr p1)))) ->
     (not_in_pset p (pset_all l))))).
Admitted.

(*Why axiom*) Lemma pset_all_elim :
  (A1:Set)
  ((p:(pointer A1))
   ((l:(pset A1))
    ((not_in_pset p (pset_all l)) ->
     ((p1:(pointer A1))
      (~(not_in_pset p1 l) -> ~((base_addr p) = (base_addr p1))))))).
Admitted.

(*Why axiom*) Lemma pset_range_intro :
  (A1:Set)
  ((p:(pointer A1))
   ((l:(pset A1))
    ((a:Z)
     ((b:Z)
      (((p1:(pointer A1)) (not_in_pset p1 l) \/
        ((i:Z) (`a <= i` /\ `i <= b` -> ~(p = (shift p1 i))))) ->
       (not_in_pset p (pset_range l a b))))))).
Admitted.

(*Why axiom*) Lemma pset_range_elim :
  (A1:Set)
  ((p:(pointer A1))
   ((l:(pset A1))
    ((a:Z)
     ((b:Z)
      ((not_in_pset p (pset_range l a b)) ->
       ((p1:(pointer A1))
        (~(not_in_pset p1 l) ->
         ((i:Z) (`a <= i` /\ `i <= b` -> ~((shift p1 i) = p)))))))))).
Admitted.

(*Why axiom*) Lemma pset_range_left_intro :
  (A1:Set)
  ((p:(pointer A1))
   ((l:(pset A1))
    ((a:Z)
     (((p1:(pointer A1)) (not_in_pset p1 l) \/
       ((i:Z) (`i <= a` -> ~(p = (shift p1 i))))) ->
      (not_in_pset p (pset_range_left l a)))))).
Admitted.

(*Why axiom*) Lemma pset_range_left_elim :
  (A1:Set)
  ((p:(pointer A1))
   ((l:(pset A1))
    ((a:Z)
     ((not_in_pset p (pset_range_left l a)) ->
      ((p1:(pointer A1))
       (~(not_in_pset p1 l) -> ((i:Z) (`i <= a` -> ~((shift p1 i) = p))))))))).
Admitted.

(*Why axiom*) Lemma pset_range_right_intro :
  (A1:Set)
  ((p:(pointer A1))
   ((l:(pset A1))
    ((a:Z)
     (((p1:(pointer A1)) (not_in_pset p1 l) \/
       ((i:Z) (`a <= i` -> ~(p = (shift p1 i))))) ->
      (not_in_pset p (pset_range_right l a)))))).
Admitted.

(*Why axiom*) Lemma pset_range_right_elim :
  (A1:Set)
  ((p:(pointer A1))
   ((l:(pset A1))
    ((a:Z)
     ((not_in_pset p (pset_range_right l a)) ->
      ((p1:(pointer A1))
       (~(not_in_pset p1 l) -> ((i:Z) (`a <= i` -> ~((shift p1 i) = p))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_all_intro :
  (A1:Set) (A2:Set)
  ((p:(pointer A1))
   ((l:(pset A2))
    ((m:(memory (pointer A1) A2))
     (((p1:(pointer A2))
       (~(not_in_pset p1 l) -> ((i:Z) ~(p = (acc m (shift p1 i)))))) ->
      (not_in_pset p (pset_acc_all l m)))))).
Admitted.

(*Why axiom*) Lemma pset_acc_all_elim :
  (A1:Set) (A2:Set)
  ((p:(pointer A1))
   ((l:(pset A2))
    ((m:(memory (pointer A1) A2))
     ((not_in_pset p (pset_acc_all l m)) ->
      ((p1:(pointer A2))
       (~(not_in_pset p1 l) -> ((i:Z) ~((acc m (shift p1 i)) = p)))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_intro :
  (A1:Set) (A2:Set)
  ((p:(pointer A1))
   ((l:(pset A2))
    ((m:(memory (pointer A1) A2))
     ((a:Z)
      ((b:Z)
       (((p1:(pointer A2))
         (~(not_in_pset p1 l) ->
          ((i:Z) (`a <= i` /\ `i <= b` -> ~(p = (acc m (shift p1 i))))))) ->
        (not_in_pset p (pset_acc_range l m a b)))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_elim :
  (A1:Set) (A2:Set)
  ((p:(pointer A1))
   ((l:(pset A2))
    ((m:(memory (pointer A1) A2))
     ((a:Z)
      ((b:Z)
       ((not_in_pset p (pset_acc_range l m a b)) ->
        ((p1:(pointer A2))
         (~(not_in_pset p1 l) ->
          ((i:Z) (`a <= i` /\ `i <= b` -> ~((acc m (shift p1 i)) = p))))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_left_intro :
  (A1:Set) (A2:Set)
  ((p:(pointer A1))
   ((l:(pset A2))
    ((m:(memory (pointer A1) A2))
     ((a:Z)
      (((p1:(pointer A2))
        (~(not_in_pset p1 l) ->
         ((i:Z) (`i <= a` -> ~(p = (acc m (shift p1 i))))))) ->
       (not_in_pset p (pset_acc_range_left l m a))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_left_elim :
  (A1:Set) (A2:Set)
  ((p:(pointer A1))
   ((l:(pset A2))
    ((m:(memory (pointer A1) A2))
     ((a:Z)
      ((not_in_pset p (pset_acc_range_left l m a)) ->
       ((p1:(pointer A2))
        (~(not_in_pset p1 l) ->
         ((i:Z) (`i <= a` -> ~((acc m (shift p1 i)) = p)))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_right_intro :
  (A1:Set) (A2:Set)
  ((p:(pointer A1))
   ((l:(pset A2))
    ((m:(memory (pointer A1) A2))
     ((a:Z)
      (((p1:(pointer A2))
        (~(not_in_pset p1 l) ->
         ((i:Z) (`a <= i` -> ~(p = (acc m (shift p1 i))))))) ->
       (not_in_pset p (pset_acc_range_right l m a))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_right_elim :
  (A1:Set) (A2:Set)
  ((p:(pointer A1))
   ((l:(pset A2))
    ((m:(memory (pointer A1) A2))
     ((a:Z)
      ((not_in_pset p (pset_acc_range_right l m a)) ->
       ((p1:(pointer A2))
        (~(not_in_pset p1 l) ->
         ((i:Z) (`a <= i` -> ~((acc m (shift p1 i)) = p)))))))))).
Admitted.

(*Why axiom*) Lemma not_assigns_trans :
  (A1:Set) (A2:Set)
  ((a:alloc_table)
   ((l:(pset A1))
    ((m1:(memory A2 A1))
     ((m2:(memory A2 A1))
      ((m3:(memory A2 A1))
       ((not_assigns a m1 m2 l) ->
        ((not_assigns a m2 m3 l) -> (not_assigns a m1 m3 l)))))))).
Admitted.

(*Why axiom*) Lemma not_assigns_refl :
  (A1:Set) (A2:Set)
  ((a:alloc_table) ((l:(pset A1)) ((m:(memory A2 A1)) (not_assigns a m m l)))).
Admitted.

(*Why predicate*) Definition valid_acc [A773:Set] [A772:Set] [m1:(memory (pointer A772) A773)]
  := ((p:(pointer A773))
      ((a:alloc_table) ((valid a p) -> (valid a (acc m1 p))))).
Implicit Arguments valid_acc.

(*Why predicate*) Definition valid_acc_range [A775:Set] [A774:Set] [m1:(memory (pointer A774) A775)] [size:Z]
  := ((p:(pointer A775))
      ((a:alloc_table)
       ((valid a p) -> (valid_range a (acc m1 p) `0` `size - 1`)))).
Implicit Arguments valid_acc_range.

(*Why axiom*) Lemma valid_acc_range_valid :
  (A1:Set) (A2:Set)
  ((m1:(memory (pointer A1) A2))
   ((size:Z)
    ((p:(pointer A2))
     ((a:alloc_table)
      ((valid_acc_range m1 size) -> ((valid a p) -> (valid a (acc m1 p)))))))).
Admitted.

(*Why predicate*) Definition separation1 [A779:Set] [A778:Set] [m1:(memory (pointer A778) A779)] [m2:(memory (pointer A778) A779)]
  := ((p:(pointer A779))
      ((a:alloc_table)
       ((valid a p) -> ~((base_addr (acc m1 p)) = (base_addr (acc m2 p)))))).
Implicit Arguments separation1.

(*Why predicate*) Definition separation1_range1 [A781:Set] [A780:Set] [m1:(memory (pointer A780) A781)] [m2:(memory (pointer A780) A781)] [size:Z]
  := ((p:(pointer A781))
      ((a:alloc_table)
       ((valid a p) ->
        ((i:Z)
         (`0 <= i` /\ `i < size` ->
          ~((base_addr (acc m1 (shift p i))) = (base_addr (acc m2 p)))))))).
Implicit Arguments separation1_range1.

(*Why predicate*) Definition separation1_range [A783:Set] [A782:Set] [m:(memory (pointer A782) A783)] [size:Z]
  := ((p:(pointer A783))
      ((a:alloc_table)
       ((valid a p) ->
        ((i1:Z)
         ((i2:Z)
          (`0 <= i1` /\ `i1 < size` ->
           (`0 <= i2` /\ `i2 < size` ->
            (`i1 <> i2` ->
             ~((base_addr (acc m (shift p i1))) =
             (base_addr (acc m (shift p i2)))))))))))).
Implicit Arguments separation1_range.

(*Why predicate*) Definition separation2 [A785:Set] [A784:Set] [m1:(memory (pointer A784) A785)] [m2:(memory (pointer A784) A785)]
  := ((p1:(pointer A785))
      ((p2:(pointer A785))
       (~(p1 = p2) -> ~((base_addr (acc m1 p1)) = (base_addr (acc m2 p2)))))).
Implicit Arguments separation2.

(*Why predicate*) Definition separation2_range1 [A787:Set] [A786:Set] [m1:(memory (pointer A786) A787)] [m2:(memory (pointer A786) A787)] [size:Z]
  := ((p:(pointer A787))
      ((q:(pointer A787))
       ((a:alloc_table)
        ((i:Z)
         (`0 <= i` /\ `i < size` ->
          ~((base_addr (acc m1 (shift p i))) = (base_addr (acc m2 q)))))))).
Implicit Arguments separation2_range1.

(*Why logic*) Definition on_heap :
  (A1:Set) alloc_table -> (pointer A1) -> Prop.
Admitted.
Implicit Arguments on_heap.

(*Why logic*) Definition on_stack :
  (A1:Set) alloc_table -> (pointer A1) -> Prop.
Admitted.
Implicit Arguments on_stack.

(*Why logic*) Definition fresh :
  (A1:Set) alloc_table -> (pointer A1) -> Prop.
Admitted.
Implicit Arguments fresh.

(*Why axiom*) Lemma fresh_not_valid :
  (A1:Set) ((a:alloc_table) ((p:(pointer A1)) ((fresh a p) -> ~(valid a p)))).
Admitted.

(*Why axiom*) Lemma fresh_not_valid_shift :
  (A1:Set)
  ((a:alloc_table)
   ((p:(pointer A1)) ((fresh a p) -> ((i:Z) ~(valid a (shift p i)))))).
Admitted.

(*Why logic*) Definition alloc_extends : alloc_table -> alloc_table -> Prop.
Admitted.

(*Why axiom*) Lemma alloc_extends_valid :
  (A1:Set)
  ((a1:alloc_table)
   ((a2:alloc_table)
    ((alloc_extends a1 a2) ->
     ((q:(pointer A1)) ((valid a1 q) -> (valid a2 q)))))).
Admitted.

(*Why axiom*) Lemma alloc_extends_valid_index :
  (A1:Set)
  ((a1:alloc_table)
   ((a2:alloc_table)
    ((alloc_extends a1 a2) ->
     ((q:(pointer A1)) ((i:Z) ((valid_index a1 q i) -> (valid_index a2 q i))))))).
Admitted.

(*Why axiom*) Lemma alloc_extends_valid_range :
  (A1:Set)
  ((a1:alloc_table)
   ((a2:alloc_table)
    ((alloc_extends a1 a2) ->
     ((q:(pointer A1))
      ((i:Z) ((j:Z) ((valid_range a1 q i j) -> (valid_range a2 q i j)))))))).
Admitted.

(*Why axiom*) Lemma alloc_extends_refl :
  ((a:alloc_table) (alloc_extends a a)).
Admitted.

(*Why axiom*) Lemma alloc_extends_trans :
  ((a1:alloc_table)
   ((a2:alloc_table)
    ((a3:alloc_table)
     ((alloc_extends a1 a2) ->
      ((alloc_extends a2 a3) -> (alloc_extends a1 a3)))))).
Admitted.

(*Why logic*) Definition free_stack :
  alloc_table -> alloc_table -> alloc_table -> Prop.
Admitted.

(*Why axiom*) Lemma free_stack_heap :
  (A1:Set)
  ((a1:alloc_table)
   ((a2:alloc_table)
    ((a3:alloc_table)
     ((free_stack a1 a2 a3) ->
      ((p:(pointer A1)) ((valid a2 p) -> ((on_heap a2 p) -> (valid a3 p)))))))).
Admitted.

(*Why axiom*) Lemma free_stack_stack :
  (A1:Set)
  ((a1:alloc_table)
   ((a2:alloc_table)
    ((a3:alloc_table)
     ((free_stack a1 a2 a3) ->
      ((p:(pointer A1)) ((valid a1 p) -> ((on_stack a1 p) -> (valid a3 p)))))))).
Admitted.

(*Why logic*) Definition null : (A1:Set) (pointer A1).
Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.










Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.


























Admitted.

Admitted.
Implicits acc [1].


Admitted.
Implicits upd [1].


Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.


Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.


Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.


Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.





Admitted.






Admitted.

Admitted.

Admitted.

Admitted.


Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.


Admitted.

Implicits assigns [1].

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.



Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

(*Why axiom*) Lemma null_not_valid :
  (A1:Set) ((a:alloc_table) ~(valid a (@null A1))).
Admitted.

