(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Why.
Require Export WhyReal.

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

Set Implicit Arguments.

(*Why type*) Definition pointer: Set ->Set.
Admitted.

(*Why type*) Definition addr: Set ->Set.
Admitted.

(*Why type*) Definition alloc_table: Set.
Admitted.


(*Why logic*) Definition null : forall (A1:Set), ((pointer) A1).
Admitted.
Set Contextual Implicit.
Implicit Arguments null.
Unset Contextual Implicit.


(*Why logic*) Definition block_length :
  forall (A1:Set), alloc_table -> ((pointer) A1) -> Z.
Admitted.

(*Why logic*) Definition base_addr :
  forall (A1:Set), ((pointer) A1) -> ((addr) A1).
Admitted.


(*Why logic*) Definition offset : forall (A1:Set), ((pointer) A1) -> Z.
Admitted.

(*Why logic*) Definition shift :
  forall (A1:Set), ((pointer) A1) -> Z -> ((pointer) A1).
Admitted.

(*Why logic*) Definition sub_pointer :
  forall (A1:Set), ((pointer) A1) -> ((pointer) A1) -> Z.
Admitted.

(*Why predicate*) Definition lt_pointer (A712:Set) (p1:((pointer) A712))
  (p2:((pointer) A712))
  := (base_addr p1) = (base_addr p2) /\ (offset p1) < (offset p2).

(*Why predicate*) Definition le_pointer (A713:Set) (p1:((pointer) A713))
  (p2:((pointer) A713))
  := (base_addr p1) = (base_addr p2) /\ (offset p1) <= (offset p2).


(*Why predicate*) Definition gt_pointer (A714:Set) (p1:((pointer) A714))
  (p2:((pointer) A714))
  := (base_addr p1) = (base_addr p2) /\ (offset p1) > (offset p2).

(*Why predicate*) Definition ge_pointer (A715:Set) (p1:((pointer) A715))
  (p2:((pointer) A715))
  := (base_addr p1) = (base_addr p2) /\ (offset p1) >= (offset p2).



(*Why predicate*) Definition valid (A716:Set) (a:alloc_table)
  (p:((pointer) A716)) := 0 <= (offset p) /\ (offset p) < (block_length a p).

(*Why predicate*) Definition valid_index (A717:Set) (a:alloc_table)
  (p:((pointer) A717)) (i:Z)
  := 0 <= ((offset p) + i) /\ ((offset p) + i) < (block_length a p).

(*Why predicate*) Definition valid_range (A718:Set) (a:alloc_table)
  (p:((pointer) A718)) (i:Z) (j:Z)
  := 0 <= ((offset p) + i) /\ i <= j /\ ((offset p) + j) < (block_length a p).

(*Why axiom*) Lemma offset_shift :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (i:Z), (offset (shift p i)) = ((offset p) + i))).
Admitted.

(*Why axiom*) Lemma shift_zero :
  forall (A1:Set), (forall (p:((pointer) A1)), (shift p 0) = p).
Admitted.

(*Why axiom*) Lemma shift_shift :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (i:Z), (forall (j:Z), (shift (shift p i) j) = (shift p (i + j))))).
Admitted.

(*Why axiom*) Lemma base_addr_shift :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (i:Z), (base_addr (shift p i)) = (base_addr p))).
Admitted.

(*Why axiom*) Lemma block_length_shift :
  forall (A1:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A1)),
    (forall (i:Z), (block_length a (shift p i)) = (block_length a p)))).
Admitted.


(*Why axiom*) Lemma base_addr_block_length :
  forall (A1:Set),
  (forall (a:alloc_table),
   (forall (p1:((pointer) A1)),
    (forall (p2:((pointer) A1)),
     ((base_addr p1) = (base_addr p2) -> (block_length a p1) =
      (block_length a p2))))).
Admitted.

(*Why axiom*) Lemma pointer_pair_1 :
  forall (A1:Set),
  (forall (p1:((pointer) A1)),
   (forall (p2:((pointer) A1)),
    ((base_addr p1) = (base_addr p2) /\ (offset p1) = (offset p2) -> p1 = p2))).
Admitted.

(*Why axiom*) Lemma pointer_pair_2 :
  forall (A1:Set),
  (forall (p1:((pointer) A1)),
   (forall (p2:((pointer) A1)),
    (p1 = p2 -> (base_addr p1) = (base_addr p2) /\ (offset p1) = (offset p2)))).
Admitted.

(*Why axiom*) Lemma neq_base_addr_neq_shift :
  forall (A1:Set),
  (forall (p1:((pointer) A1)),
   (forall (p2:((pointer) A1)),
    (forall (i:Z),
     (forall (j:Z),
      (~((base_addr p1) = (base_addr p2)) -> ~((shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma neq_offset_neq_shift :
  forall (A1:Set),
  (forall (p1:((pointer) A1)),
   (forall (p2:((pointer) A1)),
    (forall (i:Z),
     (forall (j:Z),
      (((offset p1) + i) <> ((offset p2) + j) ->
       ~((shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma eq_offset_eq_shift :
  forall (A1:Set),
  (forall (p1:((pointer) A1)),
   (forall (p2:((pointer) A1)),
    (forall (i:Z),
     (forall (j:Z),
      ((base_addr p1) = (base_addr p2) ->
       (((offset p1) + i) = ((offset p2) + j) -> (shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma valid_index_valid_shift :
  forall (A1:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A1)),
    (forall (i:Z), ((valid_index a p i) -> (valid a (shift p i)))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid_shift :
  forall (A1:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A1)),
    (forall (i:Z),
     (forall (j:Z),
      (forall (k:Z),
       ((valid_range a p i j) -> (i <= k /\ k <= j -> (valid a (shift p k))))))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid :
  forall (A1:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A1)),
    (forall (i:Z),
     (forall (j:Z),
      ((valid_range a p i j) -> (i <= 0 /\ 0 <= j -> (valid a p))))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid_index :
  forall (A1:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A1)),
    (forall (i:Z),
     (forall (j:Z),
      (forall (k:Z),
       ((valid_range a p i j) -> (i <= k /\ k <= j -> (valid_index a p k)))))))).
Admitted.

(*Why axiom*) Lemma sub_pointer_def :
  forall (A1:Set),
  (forall (p1:((pointer) A1)),
   (forall (p2:((pointer) A1)),
    ((base_addr p1) = (base_addr p2) -> (sub_pointer p1 p2) =
     ((offset p1) - (offset p2))))).
Admitted.









(*Why type*) Definition memory: Set -> Set ->Set.
Admitted.

(*Why logic*) Definition acc :
  forall (A1:Set), forall (A2:Set), ((memory) A1 A2) -> ((pointer) A2) -> A1.
Admitted.
Implicit Arguments acc.


(*Why logic*) Definition upd :
  forall (A1:Set), forall (A2:Set), ((memory) A1 A2) -> ((pointer) A2)
  -> A1 -> ((memory) A1 A2).
Admitted.
Implicit Arguments upd.


(*Why axiom*) Lemma acc_upd :
  forall (A1:Set), forall (A2:Set),
  (forall (m:((memory) A1 A2)),
   (forall (p:((pointer) A2)), (forall (a:A1), (acc (upd m p a) p) = a))).
Admitted.

(*Why axiom*) Lemma acc_upd_eq :
  forall (A1:Set), forall (A2:Set),
  (forall (m:((memory) A1 A2)),
   (forall (p1:((pointer) A2)),
    (forall (p2:((pointer) A2)),
     (forall (a:A1), (p1 = p2 -> (acc (upd m p1 a) p2) = a))))).
Admitted.

(*Why axiom*) Lemma acc_upd_neq :
  forall (A1:Set), forall (A2:Set),
  (forall (m:((memory) A1 A2)),
   (forall (p1:((pointer) A2)),
    (forall (p2:((pointer) A2)),
     (forall (a:A1), (~(p1 = p2) -> (acc (upd m p1 a) p2) = (acc m p2)))))).
Admitted.

(*Why axiom*) Lemma false_not_true : ~(false = true).
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

(*Why logic*) Definition pset_star :
  forall (A1:Set), forall (A2:Set), ((pset) A2) -> ((memory) ((pointer) A1)
  A2) -> ((pset) A1).
Admitted.

(*Why logic*) Definition pset_all :
  forall (A1:Set), ((pset) A1) -> ((pset) A1).
Admitted.

(*Why logic*) Definition pset_range :
  forall (A1:Set), ((pset) A1) -> Z -> Z -> ((pset) A1).
Admitted.

(*Why logic*) Definition pset_range_left :
  forall (A1:Set), ((pset) A1) -> Z -> ((pset) A1).
Admitted.

(*Why logic*) Definition pset_range_right :
  forall (A1:Set), ((pset) A1) -> Z -> ((pset) A1).
Admitted.

(*Why logic*) Definition pset_acc_all :
  forall (A1:Set), forall (A2:Set), ((pset) A2) -> ((memory) ((pointer) A1)
  A2) -> ((pset) A1).
Admitted.

(*Why logic*) Definition pset_acc_range :
  forall (A1:Set), forall (A2:Set), ((pset) A2) -> ((memory) ((pointer) A1)
  A2) -> Z -> Z -> ((pset) A1).
Admitted.

(*Why logic*) Definition pset_acc_range_left :
  forall (A1:Set), forall (A2:Set), ((pset) A2) -> ((memory) ((pointer) A1)
  A2) -> Z -> ((pset) A1).
Admitted.

(*Why logic*) Definition pset_acc_range_right :
  forall (A1:Set), forall (A2:Set), ((pset) A2) -> ((memory) ((pointer) A1)
  A2) -> Z -> ((pset) A1).
Admitted.

(*Why logic*) Definition pset_union :
  forall (A1:Set), ((pset) A1) -> ((pset) A1) -> ((pset) A1).
Admitted.


(*Why logic*) Definition not_in_pset :
  forall (A1:Set), ((pointer) A1) -> ((pset) A1) -> Prop.
Admitted.


(*Why predicate*) Definition not_assigns (A764:Set)
  (A763:Set) (a:alloc_table) (m1:((memory) A763 A764)) (m2:((memory) A763
  A764)) (l:((pset) A764))
  := (forall (p:((pointer) A764)),
      ((valid a p) -> ((not_in_pset p l) -> (acc m2 p) = (acc m1 p)))).
Implicit Arguments not_assigns.

(*Why axiom*) Lemma pset_empty_intro :
  forall (A1:Set), (forall (p:((pointer) A1)), (not_in_pset p pset_empty)).
Admitted.

(*Why axiom*) Lemma pset_singleton_intro :
  forall (A1:Set),
  (forall (p1:((pointer) A1)),
   (forall (p2:((pointer) A1)),
    (~(p1 = p2) -> (not_in_pset p1 (pset_singleton p2))))).
Admitted.

(*Why axiom*) Lemma not_not_in_singleton :
  forall (A1:Set),
  (forall (p:((pointer) A1)), ~(not_in_pset p (pset_singleton p))).
Admitted.

(*Why axiom*) Lemma pset_union_intro :
  forall (A1:Set),
  (forall (l1:((pset) A1)),
   (forall (l2:((pset) A1)),
    (forall (p:((pointer) A1)),
     ((not_in_pset p l1) /\ (not_in_pset p l2) ->
      (not_in_pset p (pset_union l1 l2)))))).
Admitted.


(*Why axiom*) Lemma pset_union_elim1 :
  forall (A1:Set),
  (forall (l1:((pset) A1)),
   (forall (l2:((pset) A1)),
    (forall (p:((pointer) A1)),
     ((not_in_pset p (pset_union l1 l2)) -> (not_in_pset p l1))))).
Admitted.

(*Why axiom*) Lemma pset_union_elim2 :
  forall (A1:Set),
  (forall (l1:((pset) A1)),
   (forall (l2:((pset) A1)),
    (forall (p:((pointer) A1)),
     ((not_in_pset p (pset_union l1 l2)) -> (not_in_pset p l2))))).
Admitted.

(*Why axiom*) Lemma pset_star_intro :
  forall (A1:Set), forall (A2:Set),
  (forall (l:((pset) A1)),
   (forall (m:((memory) ((pointer) A2) A1)),
    (forall (p:((pointer) A2)),
     ((forall (p1:((pointer) A1)), (p = (acc m p1) -> (not_in_pset p1 l))) ->
      (not_in_pset p (pset_star l m)))))).
Admitted.

(*Why axiom*) Lemma pset_star_elim :
  forall (A1:Set), forall (A2:Set),
  (forall (l:((pset) A1)),
   (forall (m:((memory) ((pointer) A2) A1)),
    (forall (p:((pointer) A2)),
     ((not_in_pset p (pset_star l m)) ->
      (forall (p1:((pointer) A1)), (p = (acc m p1) -> (not_in_pset p1 l))))))).
Admitted.

(*Why axiom*) Lemma pset_all_intro :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A1)),
    ((forall (p1:((pointer) A1)),
      (~(not_in_pset p1 l) -> ~((base_addr p) = (base_addr p1)))) ->
     (not_in_pset p (pset_all l))))).
Admitted.

(*Why axiom*) Lemma pset_all_elim :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A1)),
    ((not_in_pset p (pset_all l)) ->
     (forall (p1:((pointer) A1)),
      (~(not_in_pset p1 l) -> ~((base_addr p) = (base_addr p1))))))).
Admitted.

(*Why axiom*) Lemma pset_range_intro :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A1)),
    (forall (a:Z),
     (forall (b:Z),
      ((forall (p1:((pointer) A1)), (not_in_pset p1 l) \/
        (forall (i:Z), (a <= i /\ i <= b -> ~(p = (shift p1 i))))) ->
       (not_in_pset p (pset_range l a b))))))).
Admitted.


(*Why axiom*) Lemma pset_range_elim :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A1)),
    (forall (a:Z),
     (forall (b:Z),
      ((not_in_pset p (pset_range l a b)) ->
       (forall (p1:((pointer) A1)),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (a <= i /\ i <= b -> ~((shift p1 i) = p)))))))))).
Admitted.

(*Why axiom*) Lemma pset_range_left_intro :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A1)),
    (forall (a:Z),
     ((forall (p1:((pointer) A1)), (not_in_pset p1 l) \/
       (forall (i:Z), (i <= a -> ~(p = (shift p1 i))))) ->
      (not_in_pset p (pset_range_left l a)))))).
Admitted.

(*Why axiom*) Lemma pset_range_left_elim :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A1)),
    (forall (a:Z),
     ((not_in_pset p (pset_range_left l a)) ->
      (forall (p1:((pointer) A1)),
       (~(not_in_pset p1 l) ->
        (forall (i:Z), (i <= a -> ~((shift p1 i) = p))))))))).
Admitted.

(*Why axiom*) Lemma pset_range_right_intro :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A1)),
    (forall (a:Z),
     ((forall (p1:((pointer) A1)), (not_in_pset p1 l) \/
       (forall (i:Z), (a <= i -> ~(p = (shift p1 i))))) ->
      (not_in_pset p (pset_range_right l a)))))).
Admitted.

(*Why axiom*) Lemma pset_range_right_elim :
  forall (A1:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A1)),
    (forall (a:Z),
     ((not_in_pset p (pset_range_right l a)) ->
      (forall (p1:((pointer) A1)),
       (~(not_in_pset p1 l) ->
        (forall (i:Z), (a <= i -> ~((shift p1 i) = p))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_all_intro :
  forall (A1:Set), forall (A2:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A2)),
    (forall (m:((memory) ((pointer) A1) A2)),
     ((forall (p1:((pointer) A2)),
       (~(not_in_pset p1 l) -> (forall (i:Z), ~(p = (acc m (shift p1 i)))))) ->
      (not_in_pset p (pset_acc_all l m)))))).
Admitted.

(*Why axiom*) Lemma pset_acc_all_elim :
  forall (A1:Set), forall (A2:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A2)),
    (forall (m:((memory) ((pointer) A1) A2)),
     ((not_in_pset p (pset_acc_all l m)) ->
      (forall (p1:((pointer) A2)),
       (~(not_in_pset p1 l) -> (forall (i:Z), ~((acc m (shift p1 i)) = p)))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_intro :
  forall (A1:Set), forall (A2:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A2)),
    (forall (m:((memory) ((pointer) A1) A2)),
     (forall (a:Z),
      (forall (b:Z),
       ((forall (p1:((pointer) A2)),
         (~(not_in_pset p1 l) ->
          (forall (i:Z), (a <= i /\ i <= b -> ~(p = (acc m (shift p1 i))))))) ->
        (not_in_pset p (pset_acc_range l m a b)))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_elim :
  forall (A1:Set), forall (A2:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A2)),
    (forall (m:((memory) ((pointer) A1) A2)),
     (forall (a:Z),
      (forall (b:Z),
       ((not_in_pset p (pset_acc_range l m a b)) ->
        (forall (p1:((pointer) A2)),
         (~(not_in_pset p1 l) ->
          (forall (i:Z), (a <= i /\ i <= b -> ~((acc m (shift p1 i)) = p))))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_left_intro :
  forall (A1:Set), forall (A2:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A2)),
    (forall (m:((memory) ((pointer) A1) A2)),
     (forall (a:Z),
      ((forall (p1:((pointer) A2)),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (i <= a -> ~(p = (acc m (shift p1 i))))))) ->
       (not_in_pset p (pset_acc_range_left l m a))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_left_elim :
  forall (A1:Set), forall (A2:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A2)),
    (forall (m:((memory) ((pointer) A1) A2)),
     (forall (a:Z),
      ((not_in_pset p (pset_acc_range_left l m a)) ->
       (forall (p1:((pointer) A2)),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (i <= a -> ~((acc m (shift p1 i)) = p)))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_right_intro :
  forall (A1:Set), forall (A2:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A2)),
    (forall (m:((memory) ((pointer) A1) A2)),
     (forall (a:Z),
      ((forall (p1:((pointer) A2)),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (a <= i -> ~(p = (acc m (shift p1 i))))))) ->
       (not_in_pset p (pset_acc_range_right l m a))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_right_elim :
  forall (A1:Set), forall (A2:Set),
  (forall (p:((pointer) A1)),
   (forall (l:((pset) A2)),
    (forall (m:((memory) ((pointer) A1) A2)),
     (forall (a:Z),
      ((not_in_pset p (pset_acc_range_right l m a)) ->
       (forall (p1:((pointer) A2)),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (a <= i -> ~((acc m (shift p1 i)) = p)))))))))).
Admitted.

(*Why axiom*) Lemma not_assigns_trans :
  forall (A1:Set), forall (A2:Set),
  (forall (a:alloc_table),
   (forall (l:((pset) A1)),
    (forall (m1:((memory) A2 A1)),
     (forall (m2:((memory) A2 A1)),
      (forall (m3:((memory) A2 A1)),
       ((not_assigns a m1 m2 l) ->
        ((not_assigns a m2 m3 l) -> (not_assigns a m1 m3 l)))))))).
Admitted.

(*Why axiom*) Lemma not_assigns_refl :
  forall (A1:Set), forall (A2:Set),
  (forall (a:alloc_table),
   (forall (l:((pset) A1)),
    (forall (m:((memory) A2 A1)), (not_assigns a m m l)))).
Admitted.


(*Why predicate*) Definition valid_acc (A804:Set)
  (A803:Set) (m1:((memory) ((pointer) A803) A804))
  := (forall (p:((pointer) A804)),
      (forall (a:alloc_table), ((valid a p) -> (valid a (acc m1 p))))).

(*Why predicate*) Definition valid_acc_range (A806:Set)
  (A805:Set) (m1:((memory) ((pointer) A805) A806)) (size:Z)
  := (forall (p:((pointer) A806)),
      (forall (a:alloc_table),
       ((valid a p) -> (valid_range a (acc m1 p) 0 (size - 1))))).

(*Why axiom*) Lemma valid_acc_range_valid :
  forall (A1:Set), forall (A2:Set),
  (forall (m1:((memory) ((pointer) A1) A2)),
   (forall (size:Z),
    (forall (p:((pointer) A2)),
     (forall (a:alloc_table),
      ((valid_acc_range m1 size) -> ((valid a p) -> (valid a (acc m1 p)))))))).
Admitted.

(*Why predicate*) Definition separation1 (A810:Set)
  (A809:Set) (m1:((memory) ((pointer) A809) A810))
  (m2:((memory) ((pointer) A809) A810))
  := (forall (p:((pointer) A810)),
      (forall (a:alloc_table),
       ((valid a p) -> ~((base_addr (acc m1 p)) = (base_addr (acc m2 p)))))).

(*Why predicate*) Definition separation1_range1 (A812:Set)
  (A811:Set) (m1:((memory) ((pointer) A811) A812))
  (m2:((memory) ((pointer) A811) A812)) (size:Z)
  := (forall (p:((pointer) A812)),
      (forall (a:alloc_table),
       ((valid a p) ->
        (forall (i:Z),
         (0 <= i /\ i < size ->
          ~((base_addr (acc m1 (shift p i))) = (base_addr (acc m2 p)))))))).

(*Why predicate*) Definition separation1_range (A814:Set)
  (A813:Set) (m:((memory) ((pointer) A813) A814)) (size:Z)
  := (forall (p:((pointer) A814)),
      (forall (a:alloc_table),
       ((valid a p) ->
        (forall (i1:Z),
         (forall (i2:Z),
          (0 <= i1 /\ i1 < size ->
           (0 <= i2 /\ i2 < size ->
            (i1 <> i2 ->
             ~((base_addr (acc m (shift p i1))) = (base_addr (acc m
                                                              (shift p i2)))))))))))).

(*Why predicate*) Definition separation2 (A816:Set)
  (A815:Set) (m1:((memory) ((pointer) A815) A816))
  (m2:((memory) ((pointer) A815) A816))
  := (forall (p1:((pointer) A816)),
      (forall (p2:((pointer) A816)),
       (~(p1 = p2) -> ~((base_addr (acc m1 p1)) = (base_addr (acc m2 p2)))))).

(*Why predicate*) Definition separation2_range1 (A818:Set)
  (A817:Set) (m1:((memory) ((pointer) A817) A818))
  (m2:((memory) ((pointer) A817) A818)) (size:Z)
  := (forall (p:((pointer) A818)),
      (forall (q:((pointer) A818)),
       (forall (a:alloc_table),
        (forall (i:Z),
         (0 <= i /\ i < size ->
          ~((base_addr (acc m1 (shift p i))) = (base_addr (acc m2 q)))))))).

(*Why logic*) Definition on_heap :
  forall (A1:Set), alloc_table -> ((pointer) A1) -> Prop.
Admitted.

(*Why logic*) Definition on_stack :
  forall (A1:Set), alloc_table -> ((pointer) A1) -> Prop.
Admitted.

(*Why logic*) Definition fresh :
  forall (A1:Set), alloc_table -> ((pointer) A1) -> Prop.
Admitted.

(*Why axiom*) Lemma fresh_not_valid :
  forall (A1:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A1)), ((fresh a p) -> ~(valid a p)))).
Admitted.

(*Why axiom*) Lemma fresh_not_valid_shift :
  forall (A1:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A1)),
    ((fresh a p) -> (forall (i:Z), ~(valid a (shift p i)))))).
Admitted.

(*Why logic*) Definition alloc_extends : alloc_table -> alloc_table -> Prop.
Admitted.

(*Why axiom*) Lemma alloc_extends_valid :
  forall (A1:Set),
  (forall (a1:alloc_table),
   (forall (a2:alloc_table),
    ((alloc_extends a1 a2) ->
     (forall (q:((pointer) A1)), ((valid a1 q) -> (valid a2 q)))))).
Admitted.

(*Why axiom*) Lemma alloc_extends_valid_index :
  forall (A1:Set),
  (forall (a1:alloc_table),
   (forall (a2:alloc_table),
    ((alloc_extends a1 a2) ->
     (forall (q:((pointer) A1)),
      (forall (i:Z), ((valid_index a1 q i) -> (valid_index a2 q i))))))).
Admitted.

(*Why axiom*) Lemma alloc_extends_valid_range :
  forall (A1:Set),
  (forall (a1:alloc_table),
   (forall (a2:alloc_table),
    ((alloc_extends a1 a2) ->
     (forall (q:((pointer) A1)),
      (forall (i:Z),
       (forall (j:Z), ((valid_range a1 q i j) -> (valid_range a2 q i j)))))))).
Admitted.

(*Why axiom*) Lemma alloc_extends_refl :
  (forall (a:alloc_table), (alloc_extends a a)).
Admitted.

(*Why axiom*) Lemma alloc_extends_trans :
  (forall (a1:alloc_table),
   (forall (a2:alloc_table),
    (forall (a3:alloc_table),
     ((alloc_extends a1 a2) ->
      ((alloc_extends a2 a3) -> (alloc_extends a1 a3)))))).
Admitted.

(*Why logic*) Definition free_stack :
  alloc_table -> alloc_table -> alloc_table -> Prop.
Admitted.

(*Why axiom*) Lemma free_stack_heap :
  forall (A1:Set),
  (forall (a1:alloc_table),
   (forall (a2:alloc_table),
    (forall (a3:alloc_table),
     ((free_stack a1 a2 a3) ->
      (forall (p:((pointer) A1)),
       ((valid a2 p) -> ((on_heap a2 p) -> (valid a3 p)))))))).
Admitted.

(*Why axiom*) Lemma free_stack_stack :
  forall (A1:Set),
  (forall (a1:alloc_table),
   (forall (a2:alloc_table),
    (forall (a3:alloc_table),
     ((free_stack a1 a2 a3) ->
      (forall (p:((pointer) A1)),
       ((valid a1 p) -> ((on_stack a1 p) -> (valid a3 p)))))))).
Admitted.

