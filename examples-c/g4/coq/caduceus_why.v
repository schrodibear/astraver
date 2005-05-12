(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Why.
Require Export WhyFloat.

Parameter addr : Set.
Parameter pointer : Set. (* = addr * Z *)
Parameter alloc_table : Set.
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






(*Why*) Parameter null : pointer.

(*Why logic*) Definition block_length : alloc_table -> pointer -> Z.
Admitted.

(*Why logic*) Definition base_addr : pointer -> addr.
Admitted.

(*Why logic*) Definition offset : pointer -> Z.
Admitted.

(*Why logic*) Definition shift : pointer -> Z -> pointer.
Admitted.

(*Why logic*) Definition sub_pointer : pointer -> pointer -> Z.
Admitted.

(*Why predicate*) Definition lt_pointer  (p1:pointer) (p2:pointer)
  := (base_addr p1) = (base_addr p2) /\ (offset p1) < (offset p2).

(*Why predicate*) Definition le_pointer  (p1:pointer) (p2:pointer)
  := (base_addr p1) = (base_addr p2) /\ (offset p1) <= (offset p2).

(*Why predicate*) Definition gt_pointer  (p1:pointer) (p2:pointer)
  := (base_addr p1) = (base_addr p2) /\ (offset p1) > (offset p2).

(*Why predicate*) Definition ge_pointer  (p1:pointer) (p2:pointer)
  := (base_addr p1) = (base_addr p2) /\ (offset p1) >= (offset p2).



(*Why predicate*) Definition valid  (a:alloc_table) (p:pointer)
  := 0 <= (offset p) /\ (offset p) < (block_length a p).

(*Why predicate*) Definition valid_index  (a:alloc_table) (p:pointer) (i:Z)
  := 0 <= ((offset p) + i) /\ ((offset p) + i) < (block_length a p).

(*Why predicate*) Definition valid_range  (a:alloc_table) (p:pointer) (i:Z)
  (j:Z)
  := 0 <= ((offset p) + i) /\ i <= j /\ ((offset p) + j) < (block_length a p).

(*Why axiom*) Lemma null_not_valid :
  (forall (a:alloc_table), ~(valid a null)).
Admitted.

(*Why axiom*) Lemma offset_shift :
  (forall (p:pointer),
   (forall (i:Z), (offset (shift p i)) = ((offset p) + i))).
Admitted.

(*Why axiom*) Lemma shift_zero : (forall (p:pointer), (shift p 0) = p).
Admitted.

(*Why axiom*) Lemma shift_shift :
  (forall (p:pointer),
   (forall (i:Z), (forall (j:Z), (shift (shift p i) j) = (shift p (i + j))))).
Admitted.

(*Why axiom*) Lemma base_addr_shift :
  (forall (p:pointer),
   (forall (i:Z), (base_addr (shift p i)) = (base_addr p))).
Admitted.

(*Why axiom*) Lemma block_length_shift :
  (forall (a:alloc_table),
   (forall (p:pointer),
    (forall (i:Z), (block_length a (shift p i)) = (block_length a p)))).
Admitted.


(*Why axiom*) Lemma base_addr_block_length :
  (forall (a:alloc_table),
   (forall (p1:pointer),
    (forall (p2:pointer),
     ((base_addr p1) = (base_addr p2) -> (block_length a p1) =
      (block_length a p2))))).
Admitted.

(*Why axiom*) Lemma pointer_pair_1 :
  (forall (p1:pointer),
   (forall (p2:pointer),
    ((base_addr p1) = (base_addr p2) /\ (offset p1) = (offset p2) -> p1 = p2))).
Admitted.

(*Why axiom*) Lemma pointer_pair_2 :
  (forall (p1:pointer),
   (forall (p2:pointer),
    (p1 = p2 -> (base_addr p1) = (base_addr p2) /\ (offset p1) = (offset p2)))).
Admitted.

(*Why axiom*) Lemma neq_base_addr_neq_shift :
  (forall (p1:pointer),
   (forall (p2:pointer),
    (forall (i:Z),
     (forall (j:Z),
      (~((base_addr p1) = (base_addr p2)) -> ~((shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma neq_offset_neq_shift :
  (forall (p1:pointer),
   (forall (p2:pointer),
    (forall (i:Z),
     (forall (j:Z),
      (((offset p1) + i) <> ((offset p2) + j) ->
       ~((shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma eq_offset_eq_shift :
  (forall (p1:pointer),
   (forall (p2:pointer),
    (forall (i:Z),
     (forall (j:Z),
      ((base_addr p1) = (base_addr p2) ->
       (((offset p1) + i) = ((offset p2) + j) -> (shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma valid_index_valid_shift :
  (forall (a:alloc_table),
   (forall (p:pointer),
    (forall (i:Z), ((valid_index a p i) -> (valid a (shift p i)))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid_shift :
  (forall (a:alloc_table),
   (forall (p:pointer),
    (forall (i:Z),
     (forall (j:Z),
      (forall (k:Z),
       ((valid_range a p i j) -> (i <= k /\ k <= j -> (valid a (shift p k))))))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid :
  (forall (a:alloc_table),
   (forall (p:pointer),
    (forall (i:Z),
     (forall (j:Z),
      ((valid_range a p i j) -> (i <= 0 /\ 0 <= j -> (valid a p))))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid_index :
  (forall (a:alloc_table),
   (forall (p:pointer),
    (forall (i:Z),
     (forall (j:Z),
      (forall (k:Z),
       ((valid_range a p i j) -> (i <= k /\ k <= j -> (valid_index a p k)))))))).
Admitted.

(*Why axiom*) Lemma sub_pointer_def :
  (forall (p1:pointer),
   (forall (p2:pointer),
    ((base_addr p1) = (base_addr p2) -> (sub_pointer p1 p2) =
     ((offset p1) - (offset p2))))).
Admitted.







(*Why logic*) Definition acc :
  forall (A43:Set), ((memory) A43) -> pointer -> A43.
Admitted.
Implicit Arguments acc.


(*Why logic*) Definition upd :
  forall (A44:Set), ((memory) A44) -> pointer -> A44 -> ((memory) A44).
Admitted.
Implicit Arguments upd.


(*Why axiom*) Lemma acc_upd :
  forall (A45:Set),
  (forall (m:((memory) A45)),
   (forall (p:pointer), (forall (a:A45), (acc (upd m p a) p) = a))).
Admitted.

(*Why axiom*) Lemma acc_upd_eq :
  forall (A46:Set),
  (forall (m:((memory) A46)),
   (forall (p1:pointer),
    (forall (p2:pointer),
     (forall (a:A46), (p1 = p2 -> (acc (upd m p1 a) p2) = a))))).
Admitted.

(*Why axiom*) Lemma acc_upd_neq :
  forall (A47:Set),
  (forall (m:((memory) A47)),
   (forall (p1:pointer),
    (forall (p2:pointer),
     (forall (a:A47), (~(p1 = p2) -> (acc (upd m p1 a) p2) = (acc m p2)))))).
Admitted.

(*Why axiom*) Lemma false_not_true : ~(false = true).
Admitted.

Parameter pset : Set.

(*Why logic*) Definition pset_empty : pset.
Admitted.

(*Why logic*) Definition pset_singleton : pointer -> pset.
Admitted.

(*Why logic*) Definition pset_star : pset -> ((memory) pointer) -> pset.
Admitted.

(*Why logic*) Definition pset_all : pset -> pset.
Admitted.

(*Why logic*) Definition pset_range : pset -> Z -> Z -> pset.
Admitted.

(*Why logic*) Definition pset_range_left : pset -> Z -> pset.
Admitted.

(*Why logic*) Definition pset_range_right : pset -> Z -> pset.
Admitted.

(*Why logic*) Definition pset_acc_all : pset -> ((memory) pointer) -> pset.
Admitted.

(*Why logic*) Definition pset_acc_range :
  pset -> ((memory) pointer) -> Z -> Z -> pset.
Admitted.

(*Why logic*) Definition pset_acc_range_left :
  pset -> ((memory) pointer) -> Z -> pset.
Admitted.

(*Why logic*) Definition pset_acc_range_right :
  pset -> ((memory) pointer) -> Z -> pset.
Admitted.

(*Why logic*) Definition pset_union : pset -> pset -> pset.
Admitted.

(*Why logic*) Definition not_in_pset : pointer -> pset -> Prop.
Admitted.

(*Why predicate*) Definition not_assigns (A48:Set) (a:alloc_table)
  (m1:((memory) A48)) (m2:((memory) A48)) (l:pset)
  := (forall (p:pointer),
      ((valid a p) -> ((not_in_pset p l) -> (acc m2 p) = (acc m1 p)))).
Implicit Arguments not_assigns.

(*Why axiom*) Lemma pset_empty_intro :
  (forall (p:pointer), (not_in_pset p pset_empty)).
Admitted.

(*Why axiom*) Lemma pset_singleton_intro :
  (forall (p1:pointer),
   (forall (p2:pointer), (~(p1 = p2) -> (not_in_pset p1 (pset_singleton p2))))).
Admitted.

(*Why axiom*) Lemma pset_singleton_elim :
  (forall (p1:pointer),
   (forall (p2:pointer), ((not_in_pset p1 (pset_singleton p2)) -> ~(p1 = p2)))).
Admitted.

(*Why axiom*) Lemma not_not_in_singleton :
  (forall (p:pointer), ~(not_in_pset p (pset_singleton p))).
Admitted.

(*Why axiom*) Lemma pset_union_intro :
  (forall (l1:pset),
   (forall (l2:pset),
    (forall (p:pointer),
     ((not_in_pset p l1) /\ (not_in_pset p l2) ->
      (not_in_pset p (pset_union l1 l2)))))).
Admitted.

(*Why axiom*) Lemma pset_union_elim1 :
  (forall (l1:pset),
   (forall (l2:pset),
    (forall (p:pointer),
     ((not_in_pset p (pset_union l1 l2)) -> (not_in_pset p l1))))).
Admitted.

(*Why axiom*) Lemma pset_union_elim2 :
  (forall (l1:pset),
   (forall (l2:pset),
    (forall (p:pointer),
     ((not_in_pset p (pset_union l1 l2)) -> (not_in_pset p l2))))).
Admitted.

(*Why axiom*) Lemma pset_star_intro :
  (forall (l:pset),
   (forall (m:((memory) pointer)),
    (forall (p:pointer),
     ((forall (p1:pointer), (p = (acc m p1) -> (not_in_pset p1 l))) ->
      (not_in_pset p (pset_star l m)))))).
Admitted.

(*Why axiom*) Lemma pset_star_elim :
  (forall (l:pset),
   (forall (m:((memory) pointer)),
    (forall (p:pointer),
     ((not_in_pset p (pset_star l m)) ->
      (forall (p1:pointer), (p = (acc m p1) -> (not_in_pset p1 l))))))).
Admitted.

(*Why axiom*) Lemma pset_all_intro :
  (forall (p:pointer),
   (forall (l:pset),
    ((forall (p1:pointer),
      (~(not_in_pset p1 l) -> ~((base_addr p) = (base_addr p1)))) ->
     (not_in_pset p (pset_all l))))).
Admitted.

(*Why axiom*) Lemma pset_all_elim :
  (forall (p:pointer),
   (forall (l:pset),
    ((not_in_pset p (pset_all l)) ->
     (forall (p1:pointer),
      (~(not_in_pset p1 l) -> ~((base_addr p) = (base_addr p1))))))).
Admitted.

(*Why axiom*) Lemma pset_range_intro :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (a:Z),
     (forall (b:Z),
      ((forall (p1:pointer), (not_in_pset p1 l) \/
        (forall (i:Z), (a <= i /\ i <= b -> ~(p = (shift p1 i))))) ->
       (not_in_pset p (pset_range l a b))))))).
Admitted.

(*Why axiom*) Lemma pset_range_elim :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (a:Z),
     (forall (b:Z),
      ((not_in_pset p (pset_range l a b)) ->
       (forall (p1:pointer),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (a <= i /\ i <= b -> ~((shift p1 i) = p)))))))))).
Admitted.

(*Why axiom*) Lemma pset_range_left_intro :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (a:Z),
     ((forall (p1:pointer), (not_in_pset p1 l) \/
       (forall (i:Z), (i <= a -> ~(p = (shift p1 i))))) ->
      (not_in_pset p (pset_range_left l a)))))).
Admitted.

(*Why axiom*) Lemma pset_range_left_elim :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (a:Z),
     ((not_in_pset p (pset_range_left l a)) ->
      (forall (p1:pointer),
       (~(not_in_pset p1 l) ->
        (forall (i:Z), (i <= a -> ~((shift p1 i) = p))))))))).
Admitted.

(*Why axiom*) Lemma pset_range_right_intro :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (a:Z),
     ((forall (p1:pointer), (not_in_pset p1 l) \/
       (forall (i:Z), (a <= i -> ~(p = (shift p1 i))))) ->
      (not_in_pset p (pset_range_right l a)))))).
Admitted.

(*Why axiom*) Lemma pset_range_right_elim :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (a:Z),
     ((not_in_pset p (pset_range_right l a)) ->
      (forall (p1:pointer),
       (~(not_in_pset p1 l) ->
        (forall (i:Z), (a <= i -> ~((shift p1 i) = p))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_all_intro :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (m:((memory) pointer)),
     ((forall (p1:pointer),
       (~(not_in_pset p1 l) -> (forall (i:Z), ~(p = (acc m (shift p1 i)))))) ->
      (not_in_pset p (pset_acc_all l m)))))).
Admitted.

(*Why axiom*) Lemma pset_acc_all_elim :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (m:((memory) pointer)),
     ((not_in_pset p (pset_acc_all l m)) ->
      (forall (p1:pointer),
       (~(not_in_pset p1 l) -> (forall (i:Z), ~((acc m (shift p1 i)) = p)))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_intro :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (m:((memory) pointer)),
     (forall (a:Z),
      (forall (b:Z),
       ((forall (p1:pointer),
         (~(not_in_pset p1 l) ->
          (forall (i:Z), (a <= i /\ i <= b -> ~(p = (acc m (shift p1 i))))))) ->
        (not_in_pset p (pset_acc_range l m a b)))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_elim :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (m:((memory) pointer)),
     (forall (a:Z),
      (forall (b:Z),
       ((not_in_pset p (pset_acc_range l m a b)) ->
        (forall (p1:pointer),
         (~(not_in_pset p1 l) ->
          (forall (i:Z), (a <= i /\ i <= b -> ~((acc m (shift p1 i)) = p))))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_left_intro :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (m:((memory) pointer)),
     (forall (a:Z),
      ((forall (p1:pointer),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (i <= a -> ~(p = (acc m (shift p1 i))))))) ->
       (not_in_pset p (pset_acc_range_left l m a))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_left_elim :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (m:((memory) pointer)),
     (forall (a:Z),
      ((not_in_pset p (pset_acc_range_left l m a)) ->
       (forall (p1:pointer),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (i <= a -> ~((acc m (shift p1 i)) = p)))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_right_intro :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (m:((memory) pointer)),
     (forall (a:Z),
      ((forall (p1:pointer),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (a <= i -> ~(p = (acc m (shift p1 i))))))) ->
       (not_in_pset p (pset_acc_range_right l m a))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_right_elim :
  (forall (p:pointer),
   (forall (l:pset),
    (forall (m:((memory) pointer)),
     (forall (a:Z),
      ((not_in_pset p (pset_acc_range_right l m a)) ->
       (forall (p1:pointer),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (a <= i -> ~((acc m (shift p1 i)) = p)))))))))).
Admitted.

(*Why axiom*) Lemma not_assigns_trans :
  forall (A49:Set),
  (forall (a:alloc_table),
   (forall (l:pset),
    (forall (m1:((memory) A49)),
     (forall (m2:((memory) A49)),
      (forall (m3:((memory) A49)),
       ((not_assigns a m1 m2 l) ->
        ((not_assigns a m2 m3 l) -> (not_assigns a m1 m3 l)))))))).
Admitted.

(*Why axiom*) Lemma not_assigns_refl :
  forall (A50:Set),
  (forall (a:alloc_table),
   (forall (l:pset), (forall (m:((memory) A50)), (not_assigns a m m l)))).
Admitted.

(*Why predicate*) Definition valid1  (m1:((memory) pointer))
  := (forall (p:pointer),
      (forall (a:alloc_table), ((valid a p) -> (valid a (acc m1 p))))).

(*Why predicate*) Definition valid1_range  (m1:((memory) pointer)) (size:Z)
  := (forall (p:pointer),
      (forall (a:alloc_table),
       ((valid a p) -> (valid_range a (acc m1 p) 0 (size - 1))))).

(*Why predicate*) Definition separation1  (m1:((memory) pointer))
  (m2:((memory) pointer))
  := (forall (p:pointer),
      (forall (a:alloc_table),
       ((valid a p) -> ~((base_addr (acc m1 p)) = (base_addr (acc m2 p)))))).

(*Why predicate*) Definition separation1_range1  (m1:((memory) pointer))
  (m2:((memory) pointer)) (size:Z)
  := (forall (p:pointer),
      (forall (a:alloc_table),
       ((valid a p) ->
        (forall (i:Z),
         (0 <= i /\ i < size ->
          ~((base_addr (acc m1 (shift p i))) = (base_addr (acc m2 p)))))))).

(*Why predicate*) Definition separation1_range  (m:((memory) pointer))
  (size:Z)
  := (forall (p:pointer),
      (forall (a:alloc_table),
       ((valid a p) ->
        (forall (i1:Z),
         (forall (i2:Z),
          (0 <= i1 /\ i1 < size ->
           (0 <= i2 /\ i2 < size ->
            (i1 <> i2 ->
             ~((base_addr (acc m (shift p i1))) = (base_addr (acc m
                                                              (shift p i2)))))))))))).

(*Why predicate*) Definition separation2  (m1:((memory) pointer))
  (m2:((memory) pointer))
  := (forall (p1:pointer),
      (forall (p2:pointer),
       (forall (a:alloc_table),
        (~(p1 = p2) -> ~((base_addr (acc m1 p1)) = (base_addr (acc m2 p2))))))).

(*Why predicate*) Definition separation2_range1  (m1:((memory) pointer))
  (m2:((memory) pointer)) (size:Z)
  := (forall (p:pointer),
      (forall (q:pointer),
       (forall (a:alloc_table),
        (forall (i:Z),
         (0 <= i /\ i < size ->
          ~((base_addr (acc m1 (shift p i))) = (base_addr (acc m2 q)))))))).

(*Why logic*) Definition on_heap : alloc_table -> pointer -> Prop.
Admitted.

(*Why logic*) Definition on_stack : alloc_table -> pointer -> Prop.
Admitted.

(*Why logic*) Definition fresh : alloc_table -> pointer -> Prop.
Admitted.

(*Why axiom*) Lemma fresh_not_valid :
  (forall (a:alloc_table),
   (forall (p:pointer),
    ((fresh a p) -> (forall (i:Z), ~(valid a (shift p i)))))).
Admitted.

(*Why logic*) Definition alloc_stack :
  pointer -> alloc_table -> alloc_table -> Prop.
Admitted.

(*Why axiom*) Lemma alloc_stack_p :
  (forall (p:pointer),
   (forall (a1:alloc_table),
    (forall (a2:alloc_table), ((alloc_stack p a1 a2) -> (valid a2 p))))).
Admitted.

(*Why axiom*) Lemma alloc_stack_valid :
  (forall (p:pointer),
   (forall (a1:alloc_table),
    (forall (a2:alloc_table),
     ((alloc_stack p a1 a2) ->
      (forall (q:pointer), ((valid a1 q) -> (valid a2 q))))))).
Admitted.

(*Why axiom*) Lemma alloc_stack_valid_range :
  (forall (p:pointer),
   (forall (a1:alloc_table),
    (forall (a2:alloc_table),
     ((alloc_stack p a1 a2) ->
      (forall (q:pointer),
       (forall (i:Z),
        (forall (j:Z), ((valid_range a1 q i j) -> (valid_range a2 q i j))))))))).
Admitted.

(*Why logic*) Definition free_heap :
  pointer -> alloc_table -> alloc_table -> Prop.
Admitted.

(*Why logic*) Definition free_stack :
  alloc_table -> alloc_table -> alloc_table -> Prop.
Admitted.

(*Why axiom*) Lemma free_stack_heap :
  (forall (a1:alloc_table),
   (forall (a2:alloc_table),
    (forall (a3:alloc_table),
     ((free_stack a1 a2 a3) ->
      (forall (p:pointer), ((valid a2 p) -> ((on_heap a2 p) -> (valid a3 p)))))))).
Admitted.

(*Why axiom*) Lemma free_stack_stack :
  (forall (a1:alloc_table),
   (forall (a2:alloc_table),
    (forall (a3:alloc_table),
     ((free_stack a1 a2 a3) ->
      (forall (p:pointer),
       ((valid a1 p) -> ((on_stack a1 p) -> (valid a3 p)))))))).
Admitted.

