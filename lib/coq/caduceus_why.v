(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Why.
Require Export WhyFloat.

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

(*Why*) Parameter null : forall (A52: Set), ((pointer) A52).

Set Contextual Implicit.
Implicit Arguments null.
Unset Contextual Implicit.

(*Why logic*) Definition block_length :
  forall (A584:Set), alloc_table -> ((pointer) A584) -> Z.
Admitted.

(*Why logic*) Definition base_addr :
  forall (A585:Set), ((pointer) A585) -> ((addr) A585).
Admitted.


(*Why logic*) Definition offset : forall (A586:Set), ((pointer) A586) -> Z.
Admitted.

(*Why logic*) Definition shift :
  forall (A587:Set), ((pointer) A587) -> Z -> ((pointer) A587).
Admitted.

(*Why logic*) Definition sub_pointer :
  forall (A588:Set), ((pointer) A588) -> ((pointer) A588) -> Z.
Admitted.

(*Why predicate*) Definition lt_pointer (A589:Set) (p1:((pointer) A589))
  (p2:((pointer) A589))
  := (base_addr p1) = (base_addr p2) /\ (offset p1) < (offset p2).

(*Why predicate*) Definition le_pointer (A590:Set) (p1:((pointer) A590))
  (p2:((pointer) A590))
  := (base_addr p1) = (base_addr p2) /\ (offset p1) <= (offset p2).

(*Why predicate*) Definition gt_pointer (A591:Set) (p1:((pointer) A591))
  (p2:((pointer) A591))
  := (base_addr p1) = (base_addr p2) /\ (offset p1) > (offset p2).

(*Why predicate*) Definition ge_pointer (A592:Set) (p1:((pointer) A592))
  (p2:((pointer) A592))
  := (base_addr p1) = (base_addr p2) /\ (offset p1) >= (offset p2).



(*Why predicate*) Definition valid (A593:Set) (a:alloc_table)
  (p:((pointer) A593)) := 0 <= (offset p) /\ (offset p) < (block_length a p).

(*Why predicate*) Definition valid_index (A594:Set) (a:alloc_table)
  (p:((pointer) A594)) (i:Z)
  := 0 <= ((offset p) + i) /\ ((offset p) + i) < (block_length a p).

(*Why predicate*) Definition valid_range (A595:Set) (a:alloc_table)
  (p:((pointer) A595)) (i:Z) (j:Z)
  := 0 <= ((offset p) + i) /\ i <= j /\ ((offset p) + j) < (block_length a p).

(*Why axiom*) Lemma offset_shift :
  forall (A596:Set),
  (forall (p:((pointer) A596)),
   (forall (i:Z), (offset (shift p i)) = ((offset p) + i))).
Admitted.

(*Why axiom*) Lemma shift_zero :
  forall (A597:Set), (forall (p:((pointer) A597)), (shift p 0) = p).
Admitted.

(*Why axiom*) Lemma shift_shift :
  forall (A598:Set),
  (forall (p:((pointer) A598)),
   (forall (i:Z), (forall (j:Z), (shift (shift p i) j) = (shift p (i + j))))).
Admitted.

(*Why axiom*) Lemma base_addr_shift :
  forall (A599:Set),
  (forall (p:((pointer) A599)),
   (forall (i:Z), (base_addr (shift p i)) = (base_addr p))).
Admitted.

(*Why axiom*) Lemma block_length_shift :
  forall (A600:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A600)),
    (forall (i:Z), (block_length a (shift p i)) = (block_length a p)))).
Admitted.


(*Why axiom*) Lemma base_addr_block_length :
  forall (A601:Set),
  (forall (a:alloc_table),
   (forall (p1:((pointer) A601)),
    (forall (p2:((pointer) A601)),
     ((base_addr p1) = (base_addr p2) -> (block_length a p1) =
      (block_length a p2))))).
Admitted.

(*Why axiom*) Lemma pointer_pair_1 :
  forall (A602:Set),
  (forall (p1:((pointer) A602)),
   (forall (p2:((pointer) A602)),
    ((base_addr p1) = (base_addr p2) /\ (offset p1) = (offset p2) -> p1 = p2))).
Admitted.

(*Why axiom*) Lemma pointer_pair_2 :
  forall (A603:Set),
  (forall (p1:((pointer) A603)),
   (forall (p2:((pointer) A603)),
    (p1 = p2 -> (base_addr p1) = (base_addr p2) /\ (offset p1) = (offset p2)))).
Admitted.

(*Why axiom*) Lemma neq_base_addr_neq_shift :
  forall (A604:Set),
  (forall (p1:((pointer) A604)),
   (forall (p2:((pointer) A604)),
    (forall (i:Z),
     (forall (j:Z),
      (~((base_addr p1) = (base_addr p2)) -> ~((shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma neq_offset_neq_shift :
  forall (A605:Set),
  (forall (p1:((pointer) A605)),
   (forall (p2:((pointer) A605)),
    (forall (i:Z),
     (forall (j:Z),
      (((offset p1) + i) <> ((offset p2) + j) ->
       ~((shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma eq_offset_eq_shift :
  forall (A606:Set),
  (forall (p1:((pointer) A606)),
   (forall (p2:((pointer) A606)),
    (forall (i:Z),
     (forall (j:Z),
      ((base_addr p1) = (base_addr p2) ->
       (((offset p1) + i) = ((offset p2) + j) -> (shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma valid_index_valid_shift :
  forall (A607:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A607)),
    (forall (i:Z), ((valid_index a p i) -> (valid a (shift p i)))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid_shift :
  forall (A608:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A608)),
    (forall (i:Z),
     (forall (j:Z),
      (forall (k:Z),
       ((valid_range a p i j) -> (i <= k /\ k <= j -> (valid a (shift p k))))))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid :
  forall (A609:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A609)),
    (forall (i:Z),
     (forall (j:Z),
      ((valid_range a p i j) -> (i <= 0 /\ 0 <= j -> (valid a p))))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid_index :
  forall (A610:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A610)),
    (forall (i:Z),
     (forall (j:Z),
      (forall (k:Z),
       ((valid_range a p i j) -> (i <= k /\ k <= j -> (valid_index a p k)))))))).
Admitted.

(*Why axiom*) Lemma sub_pointer_def :
  forall (A611:Set),
  (forall (p1:((pointer) A611)),
   (forall (p2:((pointer) A611)),
    ((base_addr p1) = (base_addr p2) -> (sub_pointer p1 p2) =
     ((offset p1) - (offset p2))))).
Admitted.









(*Why type*) Definition memory: Set -> Set ->Set.
Admitted.

(*Why logic*) Definition acc :
  forall (A612:Set), forall (A613:Set), ((memory) A612 A613)
  -> ((pointer) A613) -> A612.
Admitted.
Implicit Arguments acc.


(*Why logic*) Definition upd :
  forall (A614:Set), forall (A615:Set), ((memory) A614 A615)
  -> ((pointer) A615) -> A614 -> ((memory) A614 A615).
Admitted.
Implicit Arguments upd.


(*Why axiom*) Lemma acc_upd :
  forall (A616:Set), forall (A617:Set),
  (forall (m:((memory) A616 A617)),
   (forall (p:((pointer) A617)), (forall (a:A616), (acc (upd m p a) p) = a))).
Admitted.

(*Why axiom*) Lemma acc_upd_eq :
  forall (A618:Set), forall (A619:Set),
  (forall (m:((memory) A618 A619)),
   (forall (p1:((pointer) A619)),
    (forall (p2:((pointer) A619)),
     (forall (a:A618), (p1 = p2 -> (acc (upd m p1 a) p2) = a))))).
Admitted.

(*Why axiom*) Lemma acc_upd_neq :
  forall (A620:Set), forall (A621:Set),
  (forall (m:((memory) A620 A621)),
   (forall (p1:((pointer) A621)),
    (forall (p2:((pointer) A621)),
     (forall (a:A620), (~(p1 = p2) -> (acc (upd m p1 a) p2) = (acc m p2)))))).
Admitted.

(*Why axiom*) Lemma false_not_true : ~(false = true).
Admitted.


(*Why type*) Definition pset: Set ->Set.
Admitted.

(*Why logic*) Definition pset_empty : forall (A622:Set), ((pset) A622).
Admitted.

Set Contextual Implicit.
Implicit Arguments pset_empty.
Unset Contextual Implicit.

(*Why logic*) Definition pset_singleton :
  forall (A623:Set), ((pointer) A623) -> ((pset) A623).
Admitted.

(*Why logic*) Definition pset_star :
  forall (A624:Set), forall (A625:Set), ((pset) A625)
  -> ((memory) ((pointer) A624) A625) -> ((pset) A624).
Admitted.

(*Why logic*) Definition pset_all :
  forall (A626:Set), ((pset) A626) -> ((pset) A626).
Admitted.

(*Why logic*) Definition pset_range :
  forall (A627:Set), ((pset) A627) -> Z -> Z -> ((pset) A627).
Admitted.

(*Why logic*) Definition pset_range_left :
  forall (A628:Set), ((pset) A628) -> Z -> ((pset) A628).
Admitted.

(*Why logic*) Definition pset_range_right :
  forall (A629:Set), ((pset) A629) -> Z -> ((pset) A629).
Admitted.

(*Why logic*) Definition pset_acc_all :
  forall (A630:Set), forall (A631:Set), ((pset) A631)
  -> ((memory) ((pointer) A630) A631) -> ((pset) A630).
Admitted.

(*Why logic*) Definition pset_acc_range :
  forall (A632:Set), forall (A633:Set), ((pset) A633)
  -> ((memory) ((pointer) A632) A633) -> Z -> Z -> ((pset) A632).
Admitted.

(*Why logic*) Definition pset_acc_range_left :
  forall (A634:Set), forall (A635:Set), ((pset) A635)
  -> ((memory) ((pointer) A634) A635) -> Z -> ((pset) A634).
Admitted.

(*Why logic*) Definition pset_acc_range_right :
  forall (A636:Set), forall (A637:Set), ((pset) A637)
  -> ((memory) ((pointer) A636) A637) -> Z -> ((pset) A636).
Admitted.

(*Why logic*) Definition pset_union :
  forall (A638:Set), ((pset) A638) -> ((pset) A638) -> ((pset) A638).
Admitted.

(*Why logic*) Definition not_in_pset :
  forall (A639:Set), ((pointer) A639) -> ((pset) A639) -> Prop.
Admitted.

(*Why predicate*) Definition not_assigns (A640:Set)
  (A641:Set) (a:alloc_table) (m1:((memory) A640 A641)) (m2:((memory) A640
  A641)) (l:((pset) A641))
  := (forall (p:((pointer) A641)),
      ((valid a p) -> ((not_in_pset p l) -> (acc m2 p) = (acc m1 p)))).
Implicit Arguments not_assigns.

(*Why axiom*) Lemma pset_empty_intro :
  forall (A642:Set),
  (forall (p:((pointer) A642)), (not_in_pset p pset_empty)).
Admitted.

(*Why axiom*) Lemma pset_singleton_intro :
  forall (A643:Set),
  (forall (p1:((pointer) A643)),
   (forall (p2:((pointer) A643)),
    (~(p1 = p2) -> (not_in_pset p1 (pset_singleton p2))))).
Admitted.

(*Why axiom*) Lemma pset_singleton_elim :
  forall (A644:Set),
  (forall (p1:((pointer) A644)),
   (forall (p2:((pointer) A644)),
    ((not_in_pset p1 (pset_singleton p2)) -> ~(p1 = p2)))).
Admitted.

(*Why axiom*) Lemma not_not_in_singleton :
  forall (A645:Set),
  (forall (p:((pointer) A645)), ~(not_in_pset p (pset_singleton p))).
Admitted.

(*Why axiom*) Lemma pset_union_intro :
  forall (A646:Set),
  (forall (l1:((pset) A646)),
   (forall (l2:((pset) A646)),
    (forall (p:((pointer) A646)),
     ((not_in_pset p l1) /\ (not_in_pset p l2) ->
      (not_in_pset p (pset_union l1 l2)))))).
Admitted.

(*Why axiom*) Lemma pset_union_elim1 :
  forall (A647:Set),
  (forall (l1:((pset) A647)),
   (forall (l2:((pset) A647)),
    (forall (p:((pointer) A647)),
     ((not_in_pset p (pset_union l1 l2)) -> (not_in_pset p l1))))).
Admitted.

(*Why axiom*) Lemma pset_union_elim2 :
  forall (A648:Set),
  (forall (l1:((pset) A648)),
   (forall (l2:((pset) A648)),
    (forall (p:((pointer) A648)),
     ((not_in_pset p (pset_union l1 l2)) -> (not_in_pset p l2))))).
Admitted.

(*Why axiom*) Lemma pset_star_intro :
  forall (A649:Set), forall (A650:Set),
  (forall (l:((pset) A649)),
   (forall (m:((memory) ((pointer) A650) A649)),
    (forall (p:((pointer) A650)),
     ((forall (p1:((pointer) A649)), (p = (acc m p1) -> (not_in_pset p1 l))) ->
      (not_in_pset p (pset_star l m)))))).
Admitted.

(*Why axiom*) Lemma pset_star_elim :
  forall (A651:Set), forall (A652:Set),
  (forall (l:((pset) A651)),
   (forall (m:((memory) ((pointer) A652) A651)),
    (forall (p:((pointer) A652)),
     ((not_in_pset p (pset_star l m)) ->
      (forall (p1:((pointer) A651)), (p = (acc m p1) -> (not_in_pset p1 l))))))).
Admitted.

(*Why axiom*) Lemma pset_all_intro :
  forall (A653:Set),
  (forall (p:((pointer) A653)),
   (forall (l:((pset) A653)),
    ((forall (p1:((pointer) A653)),
      (~(not_in_pset p1 l) -> ~((base_addr p) = (base_addr p1)))) ->
     (not_in_pset p (pset_all l))))).
Admitted.

(*Why axiom*) Lemma pset_all_elim :
  forall (A654:Set),
  (forall (p:((pointer) A654)),
   (forall (l:((pset) A654)),
    ((not_in_pset p (pset_all l)) ->
     (forall (p1:((pointer) A654)),
      (~(not_in_pset p1 l) -> ~((base_addr p) = (base_addr p1))))))).
Admitted.

(*Why axiom*) Lemma pset_range_intro :
  forall (A655:Set),
  (forall (p:((pointer) A655)),
   (forall (l:((pset) A655)),
    (forall (a:Z),
     (forall (b:Z),
      ((forall (p1:((pointer) A655)), (not_in_pset p1 l) \/
        (forall (i:Z), (a <= i /\ i <= b -> ~(p = (shift p1 i))))) ->
       (not_in_pset p (pset_range l a b))))))).
Admitted.

(*Why axiom*) Lemma pset_range_elim :
  forall (A656:Set),
  (forall (p:((pointer) A656)),
   (forall (l:((pset) A656)),
    (forall (a:Z),
     (forall (b:Z),
      ((not_in_pset p (pset_range l a b)) ->
       (forall (p1:((pointer) A656)),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (a <= i /\ i <= b -> ~((shift p1 i) = p)))))))))).
Admitted.

(*Why axiom*) Lemma pset_range_left_intro :
  forall (A657:Set),
  (forall (p:((pointer) A657)),
   (forall (l:((pset) A657)),
    (forall (a:Z),
     ((forall (p1:((pointer) A657)), (not_in_pset p1 l) \/
       (forall (i:Z), (i <= a -> ~(p = (shift p1 i))))) ->
      (not_in_pset p (pset_range_left l a)))))).
Admitted.

(*Why axiom*) Lemma pset_range_left_elim :
  forall (A658:Set),
  (forall (p:((pointer) A658)),
   (forall (l:((pset) A658)),
    (forall (a:Z),
     ((not_in_pset p (pset_range_left l a)) ->
      (forall (p1:((pointer) A658)),
       (~(not_in_pset p1 l) ->
        (forall (i:Z), (i <= a -> ~((shift p1 i) = p))))))))).
Admitted.

(*Why axiom*) Lemma pset_range_right_intro :
  forall (A659:Set),
  (forall (p:((pointer) A659)),
   (forall (l:((pset) A659)),
    (forall (a:Z),
     ((forall (p1:((pointer) A659)), (not_in_pset p1 l) \/
       (forall (i:Z), (a <= i -> ~(p = (shift p1 i))))) ->
      (not_in_pset p (pset_range_right l a)))))).
Admitted.

(*Why axiom*) Lemma pset_range_right_elim :
  forall (A660:Set),
  (forall (p:((pointer) A660)),
   (forall (l:((pset) A660)),
    (forall (a:Z),
     ((not_in_pset p (pset_range_right l a)) ->
      (forall (p1:((pointer) A660)),
       (~(not_in_pset p1 l) ->
        (forall (i:Z), (a <= i -> ~((shift p1 i) = p))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_all_intro :
  forall (A661:Set), forall (A662:Set),
  (forall (p:((pointer) A661)),
   (forall (l:((pset) A662)),
    (forall (m:((memory) ((pointer) A661) A662)),
     ((forall (p1:((pointer) A662)),
       (~(not_in_pset p1 l) -> (forall (i:Z), ~(p = (acc m (shift p1 i)))))) ->
      (not_in_pset p (pset_acc_all l m)))))).
Admitted.

(*Why axiom*) Lemma pset_acc_all_elim :
  forall (A663:Set), forall (A664:Set),
  (forall (p:((pointer) A663)),
   (forall (l:((pset) A664)),
    (forall (m:((memory) ((pointer) A663) A664)),
     ((not_in_pset p (pset_acc_all l m)) ->
      (forall (p1:((pointer) A664)),
       (~(not_in_pset p1 l) -> (forall (i:Z), ~((acc m (shift p1 i)) = p)))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_intro :
  forall (A665:Set), forall (A666:Set),
  (forall (p:((pointer) A665)),
   (forall (l:((pset) A666)),
    (forall (m:((memory) ((pointer) A665) A666)),
     (forall (a:Z),
      (forall (b:Z),
       ((forall (p1:((pointer) A666)),
         (~(not_in_pset p1 l) ->
          (forall (i:Z), (a <= i /\ i <= b -> ~(p = (acc m (shift p1 i))))))) ->
        (not_in_pset p (pset_acc_range l m a b)))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_elim :
  forall (A667:Set), forall (A668:Set),
  (forall (p:((pointer) A667)),
   (forall (l:((pset) A668)),
    (forall (m:((memory) ((pointer) A667) A668)),
     (forall (a:Z),
      (forall (b:Z),
       ((not_in_pset p (pset_acc_range l m a b)) ->
        (forall (p1:((pointer) A668)),
         (~(not_in_pset p1 l) ->
          (forall (i:Z), (a <= i /\ i <= b -> ~((acc m (shift p1 i)) = p))))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_left_intro :
  forall (A669:Set), forall (A670:Set),
  (forall (p:((pointer) A669)),
   (forall (l:((pset) A670)),
    (forall (m:((memory) ((pointer) A669) A670)),
     (forall (a:Z),
      ((forall (p1:((pointer) A670)),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (i <= a -> ~(p = (acc m (shift p1 i))))))) ->
       (not_in_pset p (pset_acc_range_left l m a))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_left_elim :
  forall (A671:Set), forall (A672:Set),
  (forall (p:((pointer) A671)),
   (forall (l:((pset) A672)),
    (forall (m:((memory) ((pointer) A671) A672)),
     (forall (a:Z),
      ((not_in_pset p (pset_acc_range_left l m a)) ->
       (forall (p1:((pointer) A672)),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (i <= a -> ~((acc m (shift p1 i)) = p)))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_right_intro :
  forall (A673:Set), forall (A674:Set),
  (forall (p:((pointer) A673)),
   (forall (l:((pset) A674)),
    (forall (m:((memory) ((pointer) A673) A674)),
     (forall (a:Z),
      ((forall (p1:((pointer) A674)),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (a <= i -> ~(p = (acc m (shift p1 i))))))) ->
       (not_in_pset p (pset_acc_range_right l m a))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_right_elim :
  forall (A675:Set), forall (A676:Set),
  (forall (p:((pointer) A675)),
   (forall (l:((pset) A676)),
    (forall (m:((memory) ((pointer) A675) A676)),
     (forall (a:Z),
      ((not_in_pset p (pset_acc_range_right l m a)) ->
       (forall (p1:((pointer) A676)),
        (~(not_in_pset p1 l) ->
         (forall (i:Z), (a <= i -> ~((acc m (shift p1 i)) = p)))))))))).
Admitted.

(*Why axiom*) Lemma not_assigns_trans :
  forall (A677:Set), forall (A678:Set),
  (forall (a:alloc_table),
   (forall (l:((pset) A677)),
    (forall (m1:((memory) A678 A677)),
     (forall (m2:((memory) A678 A677)),
      (forall (m3:((memory) A678 A677)),
       ((not_assigns a m1 m2 l) ->
        ((not_assigns a m2 m3 l) -> (not_assigns a m1 m3 l)))))))).
Admitted.

(*Why axiom*) Lemma not_assigns_refl :
  forall (A679:Set), forall (A680:Set),
  (forall (a:alloc_table),
   (forall (l:((pset) A679)),
    (forall (m:((memory) A680 A679)), (not_assigns a m m l)))).
Admitted.

(*Why predicate*) Definition valid1 (A681:Set)
  (A682:Set) (m1:((memory) ((pointer) A681) A682))
  := (forall (p:((pointer) A682)),
      (forall (a:alloc_table), ((valid a p) -> (valid a (acc m1 p))))).

(*Why predicate*) Definition valid1_range (A683:Set)
  (A684:Set) (m1:((memory) ((pointer) A683) A684)) (size:Z)
  := (forall (p:((pointer) A684)),
      (forall (a:alloc_table),
       ((valid a p) -> (valid_range a (acc m1 p) 0 (size - 1))))).

(*Why predicate*) Definition separation1 (A685:Set)
  (A686:Set) (m1:((memory) ((pointer) A685) A686))
  (m2:((memory) ((pointer) A685) A686))
  := (forall (p:((pointer) A686)),
      (forall (a:alloc_table),
       ((valid a p) -> ~((base_addr (acc m1 p)) = (base_addr (acc m2 p)))))).

(*Why predicate*) Definition separation1_range1 (A687:Set)
  (A688:Set) (m1:((memory) ((pointer) A687) A688))
  (m2:((memory) ((pointer) A687) A688)) (size:Z)
  := (forall (p:((pointer) A688)),
      (forall (a:alloc_table),
       ((valid a p) ->
        (forall (i:Z),
         (0 <= i /\ i < size ->
          ~((base_addr (acc m1 (shift p i))) = (base_addr (acc m2 p)))))))).

(*Why predicate*) Definition separation1_range (A689:Set)
  (A690:Set) (m:((memory) ((pointer) A689) A690)) (size:Z)
  := (forall (p:((pointer) A690)),
      (forall (a:alloc_table),
       ((valid a p) ->
        (forall (i1:Z),
         (forall (i2:Z),
          (0 <= i1 /\ i1 < size ->
           (0 <= i2 /\ i2 < size ->
            (i1 <> i2 ->
             ~((base_addr (acc m (shift p i1))) = (base_addr (acc m
                                                              (shift p i2)))))))))))).

(*Why predicate*) Definition separation2 (A691:Set)
  (A692:Set) (m1:((memory) ((pointer) A691) A692))
  (m2:((memory) ((pointer) A691) A692))
  := (forall (p1:((pointer) A692)),
      (forall (p2:((pointer) A692)),
       (forall (a:alloc_table),
        (~(p1 = p2) -> ~((base_addr (acc m1 p1)) = (base_addr (acc m2 p2))))))).

(*Why predicate*) Definition separation2_range1 (A693:Set)
  (A694:Set) (m1:((memory) ((pointer) A693) A694))
  (m2:((memory) ((pointer) A693) A694)) (size:Z)
  := (forall (p:((pointer) A694)),
      (forall (q:((pointer) A694)),
       (forall (a:alloc_table),
        (forall (i:Z),
         (0 <= i /\ i < size ->
          ~((base_addr (acc m1 (shift p i))) = (base_addr (acc m2 q)))))))).

(*Why logic*) Definition on_heap :
  forall (A695:Set), alloc_table -> ((pointer) A695) -> Prop.
Admitted.

(*Why logic*) Definition on_stack :
  forall (A696:Set), alloc_table -> ((pointer) A696) -> Prop.
Admitted.

(*Why logic*) Definition fresh :
  forall (A697:Set), alloc_table -> ((pointer) A697) -> Prop.
Admitted.

(*Why axiom*) Lemma fresh_not_valid :
  forall (A698:Set),
  (forall (a:alloc_table),
   (forall (p:((pointer) A698)),
    ((fresh a p) -> (forall (i:Z), ~(valid a (shift p i)))))).
Admitted.

(*Why logic*) Definition alloc_stack :
  forall (A699:Set), ((pointer) A699) -> alloc_table -> alloc_table -> Prop.
Admitted.

(*Why axiom*) Lemma alloc_stack_p :
  forall (A700:Set),
  (forall (p:((pointer) A700)),
   (forall (a1:alloc_table),
    (forall (a2:alloc_table), ((alloc_stack p a1 a2) -> (valid a2 p))))).
Admitted.

(*Why axiom*) Lemma alloc_stack_valid :
  forall (A701:Set), forall (A702:Set),
  (forall (p:((pointer) A701)),
   (forall (a1:alloc_table),
    (forall (a2:alloc_table),
     ((alloc_stack p a1 a2) ->
      (forall (q:((pointer) A702)), ((valid a1 q) -> (valid a2 q))))))).
Admitted.

(*Why axiom*) Lemma alloc_stack_valid_index :
  forall (A703:Set), forall (A704:Set),
  (forall (p:((pointer) A703)),
   (forall (a1:alloc_table),
    (forall (a2:alloc_table),
     ((alloc_stack p a1 a2) ->
      (forall (q:((pointer) A704)),
       (forall (i:Z), ((valid_index a1 q i) -> (valid_index a2 q i)))))))).
Admitted.

(*Why axiom*) Lemma alloc_stack_valid_range :
  forall (A705:Set), forall (A706:Set),
  (forall (p:((pointer) A705)),
   (forall (a1:alloc_table),
    (forall (a2:alloc_table),
     ((alloc_stack p a1 a2) ->
      (forall (q:((pointer) A706)),
       (forall (i:Z),
        (forall (j:Z), ((valid_range a1 q i j) -> (valid_range a2 q i j))))))))).
Admitted.

(*Why logic*) Definition free_heap :
  forall (A707:Set), ((pointer) A707) -> alloc_table -> alloc_table -> Prop.
Admitted.

(*Why logic*) Definition free_stack :
  alloc_table -> alloc_table -> alloc_table -> Prop.
Admitted.

(*Why axiom*) Lemma free_stack_heap :
  forall (A708:Set),
  (forall (a1:alloc_table),
   (forall (a2:alloc_table),
    (forall (a3:alloc_table),
     ((free_stack a1 a2 a3) ->
      (forall (p:((pointer) A708)),
       ((valid a2 p) -> ((on_heap a2 p) -> (valid a3 p)))))))).
Admitted.

(*Why axiom*) Lemma free_stack_stack :
  forall (A709:Set),
  (forall (a1:alloc_table),
   (forall (a2:alloc_table),
    (forall (a3:alloc_table),
     ((free_stack a1 a2 a3) ->
      (forall (p:((pointer) A709)),
       ((valid a1 p) -> ((on_stack a1 p) -> (valid a3 p)))))))).
Admitted.

