(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require WhyFloat.

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





<<<<<<< caduceus_why.v



(*Why type*) Definition pointer: Set ->Set.
=======
>>>>>>> 1.38

























































Admitted.

(*Why type*) Definition addr: Set ->Set.
Admitted.

(*Why type*) Definition alloc_table: Set.
Admitted.

(*Why*) Parameter null : (A43: Set)((pointer) A43).





(*Why logic*) Definition block_length :
  (A433:Set) alloc_table -> ((pointer) A433) -> Z.
Admitted.

(*Why logic*) Definition base_addr :
  (A434:Set) ((pointer) A434) -> ((addr) A434).
Admitted.

(*Why logic*) Definition offset : (A435:Set) ((pointer) A435) -> Z.
Admitted.

(*Why logic*) Definition shift :
  (A436:Set) ((pointer) A436) -> Z -> ((pointer) A436).
Admitted.

Admitted.

(*Why logic*) Definition sub_pointer :
  (A437:Set) ((pointer) A437) -> ((pointer) A437) -> Z.
Admitted.

(*Why predicate*) Definition lt_pointer [A438:Set] [p1:((pointer) A438)]
  [p2:((pointer) A438)]
  := (base_addr p1) = (base_addr p2) /\ `(offset p1) < (offset p2)`.

(*Why predicate*) Definition le_pointer [A439:Set] [p1:((pointer) A439)]
  [p2:((pointer) A439)]
  := (base_addr p1) = (base_addr p2) /\ `(offset p1) <= (offset p2)`.

(*Why predicate*) Definition gt_pointer [A440:Set] [p1:((pointer) A440)]
  [p2:((pointer) A440)]
  := (base_addr p1) = (base_addr p2) /\ `(offset p1) > (offset p2)`.

(*Why predicate*) Definition ge_pointer [A441:Set] [p1:((pointer) A441)]
  [p2:((pointer) A441)]
  := (base_addr p1) = (base_addr p2) /\ `(offset p1) >= (offset p2)`.



(*Why predicate*) Definition valid [A442:Set] [a:alloc_table]
  [p:((pointer) A442)]
  := `0 <= (offset p)` /\ `(offset p) < (block_length a p)`.

(*Why predicate*) Definition valid_index [A443:Set] [a:alloc_table]
  [p:((pointer) A443)] [i:Z]
  := `0 <= (offset p) + i` /\ `(offset p) + i < (block_length a p)`.

(*Why predicate*) Definition valid_range [A444:Set] [a:alloc_table]
  [p:((pointer) A444)] [i:Z] [j:Z]
  := `0 <= (offset p) + i` /\ `i <= j` /\
     `(offset p) + j < (block_length a p)`.

Admitted.

(*Why axiom*) Lemma offset_shift :
  (A445:Set)
  ((p:((pointer) A445)) ((i:Z) `(offset (shift p i)) = (offset p) + i`)).
Admitted.

(*Why axiom*) Lemma shift_zero :
  (A446:Set) ((p:((pointer) A446)) (shift p `0`) = p).
Admitted.

(*Why axiom*) Lemma shift_shift :
  (A447:Set)
  ((p:((pointer) A447))
   ((i:Z) ((j:Z) (shift (shift p i) j) = (shift p `i + j`)))).
Admitted.

(*Why axiom*) Lemma base_addr_shift :
  (A448:Set)
  ((p:((pointer) A448)) ((i:Z) (base_addr (shift p i)) = (base_addr p))).
Admitted.

(*Why axiom*) Lemma block_length_shift :
  (A449:Set)
  ((a:alloc_table)
   ((p:((pointer) A449))
    ((i:Z) `(block_length a (shift p i)) = (block_length a p)`))).
Admitted.

Admitted.

Admitted.

(*Why axiom*) Lemma base_addr_block_length :
  (A450:Set)
  ((a:alloc_table)
   ((p1:((pointer) A450))
    ((p2:((pointer) A450))
     ((base_addr p1) = (base_addr p2) ->
      `(block_length a p1) = (block_length a p2)`)))).
Admitted.

(*Why axiom*) Lemma pointer_pair_1 :
  (A451:Set)
  ((p1:((pointer) A451))
   ((p2:((pointer) A451))
    ((base_addr p1) = (base_addr p2) /\ `(offset p1) = (offset p2)` ->
     p1 = p2))).
Admitted.

(*Why axiom*) Lemma pointer_pair_2 :
  (A452:Set)
  ((p1:((pointer) A452))
   ((p2:((pointer) A452))
    (p1 = p2 -> (base_addr p1) = (base_addr p2) /\
     `(offset p1) = (offset p2)`))).
Admitted.

(*Why axiom*) Lemma neq_base_addr_neq_shift :
  (A453:Set)
  ((p1:((pointer) A453))
   ((p2:((pointer) A453))
    ((i:Z)
     ((j:Z)
      (~((base_addr p1) = (base_addr p2)) -> ~((shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma neq_offset_neq_shift :
  (A454:Set)
  ((p1:((pointer) A454))
   ((p2:((pointer) A454))
    ((i:Z)
     ((j:Z)
      (`(offset p1) + i <> (offset p2) + j` -> ~((shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma eq_offset_eq_shift :
  (A455:Set)
  ((p1:((pointer) A455))
   ((p2:((pointer) A455))
    ((i:Z)
     ((j:Z)
      ((base_addr p1) = (base_addr p2) ->
       (`(offset p1) + i = (offset p2) + j` -> (shift p1 i) = (shift p2 j))))))).
Admitted.

(*Why axiom*) Lemma valid_index_valid_shift :
  (A456:Set)
  ((a:alloc_table)
   ((p:((pointer) A456))
    ((i:Z) ((valid_index a p i) -> (valid a (shift p i)))))).
Admitted.

Admitted.

Admitted.

(*Why axiom*) Lemma valid_range_valid_shift :
  (A457:Set)
  ((a:alloc_table)
   ((p:((pointer) A457))
    ((i:Z)
     ((j:Z)
      ((k:Z)
       ((valid_range a p i j) ->
        (`i <= k` /\ `k <= j` -> (valid a (shift p k))))))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid :
  (A458:Set)
  ((a:alloc_table)
   ((p:((pointer) A458))
    ((i:Z)
     ((j:Z) ((valid_range a p i j) -> (`i <= 0` /\ `0 <= j` -> (valid a p))))))).
Admitted.

(*Why axiom*) Lemma valid_range_valid_index :
  (A459:Set)
  ((a:alloc_table)
   ((p:((pointer) A459))
    ((i:Z)
     ((j:Z)
      ((k:Z)
       ((valid_range a p i j) ->
        (`i <= k` /\ `k <= j` -> (valid_index a p k)))))))).
Admitted.

(*Why axiom*) Lemma sub_pointer_def :
  (A460:Set)
  ((p1:((pointer) A460))
   ((p2:((pointer) A460))
    ((base_addr p1) = (base_addr p2) ->
     `(sub_pointer p1 p2) = (offset p1) - (offset p2)`))).
Admitted.







<<<<<<< caduceus_why.v

(*Why type*) Definition memory: Set -> Set ->Set.
=======
>>>>>>> 1.38



















Admitted.

(*Why logic*) Definition acc :
  (A461:Set) (A462:Set) ((memory) A462 A461) -> ((pointer) A461) -> A462.
Admitted.
Implicits acc [1].


(*Why logic*) Definition upd :
  (A463:Set) (A464:Set) ((memory) A464 A463) -> ((pointer) A463)
  -> A464 -> ((memory) A464 A463).
Admitted.
Implicits upd [1].


(*Why axiom*) Lemma acc_upd :
  (A465:Set) (A466:Set)
  ((m:((memory) A466 A465))
   ((p:((pointer) A465)) ((a:A466) (acc (upd m p a) p) = a))).
Admitted.

(*Why axiom*) Lemma acc_upd_eq :
  (A467:Set) (A468:Set)
  ((m:((memory) A468 A467))
   ((p1:((pointer) A467))
    ((p2:((pointer) A467)) ((a:A468) (p1 = p2 -> (acc (upd m p1 a) p2) = a))))).
Admitted.

(*Why axiom*) Lemma acc_upd_neq :
  (A469:Set) (A470:Set)
  ((m:((memory) A470 A469))
   ((p1:((pointer) A469))
    ((p2:((pointer) A469))
     ((a:A470) (~(p1 = p2) -> (acc (upd m p1 a) p2) = (acc m p2)))))).
Admitted.

(*Why axiom*) Lemma false_not_true : ~(false = true).
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


(*Why type*) Definition pset: Set ->Set.
Admitted.

(*Why logic*) Definition pset_empty : (A471:Set) ((pset) A471).
Admitted.

(*Why logic*) Definition pset_singleton :
  (A472:Set) ((pointer) A472) -> ((pset) A472).
Admitted.

(*Why logic*) Definition pset_star :
  (A473:Set) (A474:Set) ((pset) A473) -> ((memory) ((pointer) A474)
  A473) -> ((pset) A474).
Admitted.

(*Why logic*) Definition pset_all :
  (A475:Set) ((pset) A475) -> ((pset) A475).
Admitted.

(*Why logic*) Definition pset_range :
  (A476:Set) ((pset) A476) -> Z -> Z -> ((pset) A476).
Admitted.

(*Why logic*) Definition pset_range_left :
  (A477:Set) ((pset) A477) -> Z -> ((pset) A477).
Admitted.

(*Why logic*) Definition pset_range_right :
  (A478:Set) ((pset) A478) -> Z -> ((pset) A478).
Admitted.

(*Why logic*) Definition pset_acc_all :
  (A479:Set) (A480:Set) ((pset) A479) -> ((memory) ((pointer) A480)
  A479) -> ((pset) A480).
Admitted.

(*Why logic*) Definition pset_acc_range :
  (A481:Set) (A482:Set) ((pset) A481) -> ((memory) ((pointer) A482) A481)
  -> Z -> Z -> ((pset) A482).
Admitted.

(*Why logic*) Definition pset_acc_range_left :
  (A483:Set) (A484:Set) ((pset) A483) -> ((memory) ((pointer) A484) A483)
  -> Z -> ((pset) A484).
Admitted.

(*Why logic*) Definition pset_acc_range_right :
  (A485:Set) (A486:Set) ((pset) A485) -> ((memory) ((pointer) A486) A485)
  -> Z -> ((pset) A486).
Admitted.

(*Why logic*) Definition pset_union :
  (A487:Set) ((pset) A487) -> ((pset) A487) -> ((pset) A487).
Admitted.

(*Why logic*) Definition not_in_pset :
  (A488:Set) ((pointer) A488) -> ((pset) A488) -> Prop.
Admitted.

(*Why predicate*) Definition not_assigns [A489:Set]
  [A490:Set] [a:alloc_table] [m1:((memory) A490 A489)] [m2:((memory) A490
  A489)] [l:((pset) A489)]
  := ((p:((pointer) A489))
      ((valid a p) -> ((not_in_pset p l) -> (acc m2 p) = (acc m1 p)))).

(*Why axiom*) Lemma pset_empty_intro :
  (A491:Set) ((p:((pointer) A491)) (not_in_pset p pset_empty)).
Admitted.

(*Why axiom*) Lemma pset_singleton_intro :
  (A492:Set)
  ((p1:((pointer) A492))
   ((p2:((pointer) A492))
    (~(p1 = p2) -> (not_in_pset p1 (pset_singleton p2))))).
Admitted.

(*Why axiom*) Lemma pset_singleton_elim :
  (A493:Set)
  ((p1:((pointer) A493))
   ((p2:((pointer) A493))
    ((not_in_pset p1 (pset_singleton p2)) -> ~(p1 = p2)))).
Admitted.

(*Why axiom*) Lemma not_not_in_singleton :
  (A494:Set) ((p:((pointer) A494)) ~(not_in_pset p (pset_singleton p))).
Admitted.

(*Why axiom*) Lemma pset_union_intro :
  (A495:Set)
  ((l1:((pset) A495))
   ((l2:((pset) A495))
    ((p:((pointer) A495))
     ((not_in_pset p l1) /\ (not_in_pset p l2) ->
      (not_in_pset p (pset_union l1 l2)))))).
Admitted.

(*Why axiom*) Lemma pset_union_elim1 :
  (A496:Set)
  ((l1:((pset) A496))
   ((l2:((pset) A496))
    ((p:((pointer) A496))
     ((not_in_pset p (pset_union l1 l2)) -> (not_in_pset p l1))))).
Admitted.

(*Why axiom*) Lemma pset_union_elim2 :
  (A497:Set)
  ((l1:((pset) A497))
   ((l2:((pset) A497))
    ((p:((pointer) A497))
     ((not_in_pset p (pset_union l1 l2)) -> (not_in_pset p l2))))).
Admitted.

(*Why axiom*) Lemma pset_star_intro :
  (A498:Set) (A499:Set)
  ((l:((pset) A499))
   ((m:((memory) ((pointer) A498) A499))
    ((p:((pointer) A498))
     (((p1:((pointer) A499)) (p = (acc m p1) -> (not_in_pset p1 l))) ->
      (not_in_pset p (pset_star l m)))))).
Admitted.

(*Why axiom*) Lemma pset_star_elim :
  (A500:Set) (A501:Set)
  ((l:((pset) A501))
   ((m:((memory) ((pointer) A500) A501))
    ((p:((pointer) A500))
     ((not_in_pset p (pset_star l m)) ->
      ((p1:((pointer) A501)) (p = (acc m p1) -> (not_in_pset p1 l))))))).
Admitted.

(*Why axiom*) Lemma pset_all_intro :
  (A502:Set)
  ((p:((pointer) A502))
   ((l:((pset) A502))
    (((p1:((pointer) A502))
      (~(not_in_pset p1 l) -> ~((base_addr p) = (base_addr p1)))) ->
     (not_in_pset p (pset_all l))))).
Admitted.

(*Why axiom*) Lemma pset_all_elim :
  (A503:Set)
  ((p:((pointer) A503))
   ((l:((pset) A503))
    ((not_in_pset p (pset_all l)) ->
     ((p1:((pointer) A503))
      (~(not_in_pset p1 l) -> ~((base_addr p) = (base_addr p1))))))).
Admitted.

(*Why axiom*) Lemma pset_range_intro :
  (A504:Set)
  ((p:((pointer) A504))
   ((l:((pset) A504))
    ((a:Z)
     ((b:Z)
      (((p1:((pointer) A504)) (not_in_pset p1 l) \/
        ((i:Z) (`a <= i` /\ `i <= b` -> ~(p = (shift p1 i))))) ->
       (not_in_pset p (pset_range l a b))))))).
Admitted.

(*Why axiom*) Lemma pset_range_elim :
  (A505:Set)
  ((p:((pointer) A505))
   ((l:((pset) A505))
    ((a:Z)
     ((b:Z)
      ((not_in_pset p (pset_range l a b)) ->
       ((p1:((pointer) A505))
        (~(not_in_pset p1 l) ->
         ((i:Z) (`a <= i` /\ `i <= b` -> ~((shift p1 i) = p)))))))))).
Admitted.

(*Why axiom*) Lemma pset_range_left_intro :
  (A506:Set)
  ((p:((pointer) A506))
   ((l:((pset) A506))
    ((a:Z)
     (((p1:((pointer) A506)) (not_in_pset p1 l) \/
       ((i:Z) (`i <= a` -> ~(p = (shift p1 i))))) ->
      (not_in_pset p (pset_range_left l a)))))).
Admitted.

(*Why axiom*) Lemma pset_range_left_elim :
  (A507:Set)
  ((p:((pointer) A507))
   ((l:((pset) A507))
    ((a:Z)
     ((not_in_pset p (pset_range_left l a)) ->
      ((p1:((pointer) A507))
       (~(not_in_pset p1 l) -> ((i:Z) (`i <= a` -> ~((shift p1 i) = p))))))))).
Admitted.

(*Why axiom*) Lemma pset_range_right_intro :
  (A508:Set)
  ((p:((pointer) A508))
   ((l:((pset) A508))
    ((a:Z)
     (((p1:((pointer) A508)) (not_in_pset p1 l) \/
       ((i:Z) (`a <= i` -> ~(p = (shift p1 i))))) ->
      (not_in_pset p (pset_range_right l a)))))).
Admitted.

(*Why axiom*) Lemma pset_range_right_elim :
  (A509:Set)
  ((p:((pointer) A509))
   ((l:((pset) A509))
    ((a:Z)
     ((not_in_pset p (pset_range_right l a)) ->
      ((p1:((pointer) A509))
       (~(not_in_pset p1 l) -> ((i:Z) (`a <= i` -> ~((shift p1 i) = p))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_all_intro :
  (A510:Set) (A511:Set)
  ((p:((pointer) A511))
   ((l:((pset) A510))
    ((m:((memory) ((pointer) A511) A510))
     (((p1:((pointer) A510))
       (~(not_in_pset p1 l) -> ((i:Z) ~(p = (acc m (shift p1 i)))))) ->
      (not_in_pset p (pset_acc_all l m)))))).
Admitted.

(*Why axiom*) Lemma pset_acc_all_elim :
  (A512:Set) (A513:Set)
  ((p:((pointer) A513))
   ((l:((pset) A512))
    ((m:((memory) ((pointer) A513) A512))
     ((not_in_pset p (pset_acc_all l m)) ->
      ((p1:((pointer) A512))
       (~(not_in_pset p1 l) -> ((i:Z) ~((acc m (shift p1 i)) = p)))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_intro :
  (A514:Set) (A515:Set)
  ((p:((pointer) A515))
   ((l:((pset) A514))
    ((m:((memory) ((pointer) A515) A514))
     ((a:Z)
      ((b:Z)
       (((p1:((pointer) A514))
         (~(not_in_pset p1 l) ->
          ((i:Z) (`a <= i` /\ `i <= b` -> ~(p = (acc m (shift p1 i))))))) ->
        (not_in_pset p (pset_acc_range l m a b)))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_elim :
  (A516:Set) (A517:Set)
  ((p:((pointer) A517))
   ((l:((pset) A516))
    ((m:((memory) ((pointer) A517) A516))
     ((a:Z)
      ((b:Z)
       ((not_in_pset p (pset_acc_range l m a b)) ->
        ((p1:((pointer) A516))
         (~(not_in_pset p1 l) ->
          ((i:Z) (`a <= i` /\ `i <= b` -> ~((acc m (shift p1 i)) = p))))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_left_intro :
  (A518:Set) (A519:Set)
  ((p:((pointer) A519))
   ((l:((pset) A518))
    ((m:((memory) ((pointer) A519) A518))
     ((a:Z)
      (((p1:((pointer) A518))
        (~(not_in_pset p1 l) ->
         ((i:Z) (`i <= a` -> ~(p = (acc m (shift p1 i))))))) ->
       (not_in_pset p (pset_acc_range_left l m a))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_left_elim :
  (A520:Set) (A521:Set)
  ((p:((pointer) A521))
   ((l:((pset) A520))
    ((m:((memory) ((pointer) A521) A520))
     ((a:Z)
      ((not_in_pset p (pset_acc_range_left l m a)) ->
       ((p1:((pointer) A520))
        (~(not_in_pset p1 l) ->
         ((i:Z) (`i <= a` -> ~((acc m (shift p1 i)) = p)))))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_right_intro :
  (A522:Set) (A523:Set)
  ((p:((pointer) A523))
   ((l:((pset) A522))
    ((m:((memory) ((pointer) A523) A522))
     ((a:Z)
      (((p1:((pointer) A522))
        (~(not_in_pset p1 l) ->
         ((i:Z) (`a <= i` -> ~(p = (acc m (shift p1 i))))))) ->
       (not_in_pset p (pset_acc_range_right l m a))))))).
Admitted.

(*Why axiom*) Lemma pset_acc_range_right_elim :
  (A524:Set) (A525:Set)
  ((p:((pointer) A525))
   ((l:((pset) A524))
    ((m:((memory) ((pointer) A525) A524))
     ((a:Z)
      ((not_in_pset p (pset_acc_range_right l m a)) ->
       ((p1:((pointer) A524))
        (~(not_in_pset p1 l) ->
         ((i:Z) (`a <= i` -> ~((acc m (shift p1 i)) = p)))))))))).
Admitted.

(*Why axiom*) Lemma not_assigns_trans :
  (A526:Set) (A527:Set)
  ((a:alloc_table)
   ((l:((pset) A527))
    ((m1:((memory) A526 A527))
     ((m2:((memory) A526 A527))
      ((m3:((memory) A526 A527))
       ((not_assigns a m1 m2 l) ->
        ((not_assigns a m2 m3 l) -> (not_assigns a m1 m3 l)))))))).
Admitted.

(*Why axiom*) Lemma not_assigns_refl :
  (A528:Set) (A529:Set)
  ((a:alloc_table)
   ((l:((pset) A529)) ((m:((memory) A528 A529)) (not_assigns a m m l)))).
Admitted.

(*Why predicate*) Definition valid1 [A530:Set]
  [A531:Set] [m1:((memory) ((pointer) A531) A530)]
  := ((p:((pointer) A530))
      ((a:alloc_table) ((valid a p) -> (valid a (acc m1 p))))).

(*Why predicate*) Definition valid1_range [A532:Set]
  [A533:Set] [m1:((memory) ((pointer) A533) A532)] [size:Z]
  := ((p:((pointer) A532))
      ((a:alloc_table)
       ((valid a p) -> (valid_range a (acc m1 p) `0` `size - 1`)))).

(*Why predicate*) Definition separation1 [A534:Set]
  [A535:Set] [m1:((memory) ((pointer) A535) A534)]
  [m2:((memory) ((pointer) A535) A534)]
  := ((p:((pointer) A534))
      ((a:alloc_table)
       ((valid a p) -> ~((base_addr (acc m1 p)) = (base_addr (acc m2 p)))))).

(*Why predicate*) Definition separation1_range1 [A536:Set]
  [A537:Set] [m1:((memory) ((pointer) A537) A536)]
  [m2:((memory) ((pointer) A537) A536)] [size:Z]
  := ((p:((pointer) A536))
      ((a:alloc_table)
       ((valid a p) ->
        ((i:Z)
         (`0 <= i` /\ `i < size` ->
          ~((base_addr (acc m1 (shift p i))) = (base_addr (acc m2 p)))))))).

(*Why predicate*) Definition separation1_range [A538:Set]
  [A539:Set] [m:((memory) ((pointer) A539) A538)] [size:Z]
  := ((p:((pointer) A538))
      ((a:alloc_table)
       ((valid a p) ->
        ((i1:Z)
         ((i2:Z)
          (`0 <= i1` /\ `i1 < size` ->
           (`0 <= i2` /\ `i2 < size` ->
            (`i1 <> i2` ->
             ~((base_addr (acc m (shift p i1))) = (base_addr (acc m
                                                              (shift p i2)))))))))))).

(*Why predicate*) Definition separation2 [A540:Set]
  [A541:Set] [m1:((memory) ((pointer) A541) A540)]
  [m2:((memory) ((pointer) A541) A540)]
  := ((p1:((pointer) A540))
      ((p2:((pointer) A540))
       ((a:alloc_table)
        (~(p1 = p2) -> ~((base_addr (acc m1 p1)) = (base_addr (acc m2 p2))))))).

(*Why predicate*) Definition separation2_range1 [A542:Set]
  [A543:Set] [m1:((memory) ((pointer) A543) A542)]
  [m2:((memory) ((pointer) A543) A542)] [size:Z]
  := ((p:((pointer) A542))
      ((q:((pointer) A542))
       ((a:alloc_table)
        ((i:Z)
         (`0 <= i` /\ `i < size` ->
          ~((base_addr (acc m1 (shift p i))) = (base_addr (acc m2 q)))))))).

(*Why logic*) Definition on_heap :
  (A544:Set) alloc_table -> ((pointer) A544) -> Prop.
Admitted.

(*Why logic*) Definition on_stack :
  (A545:Set) alloc_table -> ((pointer) A545) -> Prop.
Admitted.

(*Why logic*) Definition fresh :
  (A546:Set) alloc_table -> ((pointer) A546) -> Prop.
Admitted.

(*Why axiom*) Lemma fresh_not_valid :
  (A547:Set)
  ((a:alloc_table)
   ((p:((pointer) A547)) ((fresh a p) -> ((i:Z) ~(valid a (shift p i)))))).
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

(*Why logic*) Definition alloc_stack :
  (A548:Set) ((pointer) A548) -> alloc_table -> alloc_table -> Prop.
Admitted.

(*Why axiom*) Lemma alloc_stack_p :
  (A549:Set)
  ((p:((pointer) A549))
   ((a1:alloc_table)
    ((a2:alloc_table) ((alloc_stack p a1 a2) -> (valid a2 p))))).
Admitted.

(*Why axiom*) Lemma alloc_stack_valid :
  (A550:Set) (A551:Set)
  ((p:((pointer) A551))
   ((a1:alloc_table)
    ((a2:alloc_table)
     ((alloc_stack p a1 a2) ->
      ((q:((pointer) A550)) ((valid a1 q) -> (valid a2 q))))))).
Admitted.

(*Why axiom*) Lemma alloc_stack_valid_index :
  (A552:Set) (A553:Set)
  ((p:((pointer) A553))
   ((a1:alloc_table)
    ((a2:alloc_table)
     ((alloc_stack p a1 a2) ->
      ((q:((pointer) A552))
       ((i:Z) ((valid_index a1 q i) -> (valid_index a2 q i)))))))).
Admitted.

(*Why axiom*) Lemma alloc_stack_valid_range :
  (A554:Set) (A555:Set)
  ((p:((pointer) A555))
   ((a1:alloc_table)
    ((a2:alloc_table)
     ((alloc_stack p a1 a2) ->
      ((q:((pointer) A554))
       ((i:Z) ((j:Z) ((valid_range a1 q i j) -> (valid_range a2 q i j))))))))).
Admitted.

(*Why logic*) Definition free_heap :
  (A556:Set) ((pointer) A556) -> alloc_table -> alloc_table -> Prop.
Admitted.

(*Why logic*) Definition free_stack :
  alloc_table -> alloc_table -> alloc_table -> Prop.
Admitted.

(*Why axiom*) Lemma free_stack_heap :
  (A557:Set)
  ((a1:alloc_table)
   ((a2:alloc_table)
    ((a3:alloc_table)
     ((free_stack a1 a2 a3) ->
      ((p:((pointer) A557))
       ((valid a2 p) -> ((on_heap a2 p) -> (valid a3 p)))))))).
Admitted.

(*Why axiom*) Lemma free_stack_stack :
  (A558:Set)
  ((a1:alloc_table)
   ((a2:alloc_table)
    ((a3:alloc_table)
     ((free_stack a1 a2 a3) ->
      ((p:((pointer) A558))
       ((valid a1 p) -> ((on_stack a1 p) -> (valid a3 p)))))))).
Admitted.

