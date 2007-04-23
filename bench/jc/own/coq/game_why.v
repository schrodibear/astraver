(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export jessie_why.

(*Why type*) Definition Hero: Set.
Admitted.

(*Why type*) Definition Sword: Set.
Admitted.

(*Why logic*) Definition Hero_inv :
  (pointer Hero) -> (memory Sword Z) -> (memory Hero bool) -> (memory Hero Z)
  -> (memory Hero (pointer Sword)) -> Prop.
Admitted.

(*Why logic*) Definition Sword_inv :
  (pointer Sword) -> (memory Sword Z) -> Prop.
Admitted.


(*Why predicate*) Definition life_inv  (dead:(memory Hero bool))
  (life:(memory Hero Z)) (this:(pointer Hero))
  := (select life this) >= 0 /\ (select life this) <= 100 /\
     (((select life this) = 0 -> (select dead this) = true)).

(*Why axiom*) Lemma Hero_inv_sem :
  (forall (sword:(memory Hero (pointer Sword))),
   (forall (life:(memory Hero Z)),
    (forall (dead:(memory Hero bool)),
     (forall (damage:(memory Sword Z)),
      (forall (inv_this:(pointer Hero)),
       ((Hero_inv inv_this damage dead life sword) <->
        (~(inv_this = (@null Hero)) ->
         (Sword_inv (select sword inv_this) damage) /\
         (life_inv dead life inv_this)))))))).
Admitted.

(*Why logic*) Definition Hero_tag : (tag_id Hero).
Admitted.

(*Why predicate*) Definition damage_inv  (damage:(memory Sword Z))
  (this:(pointer Sword)) := (select damage this) > 0.

(*Why axiom*) Lemma Sword_inv_sem :
  (forall (damage:(memory Sword Z)),
   (forall (inv_this:(pointer Sword)),
    ((Sword_inv inv_this damage) <->
     (~(inv_this = (@null Sword)) -> (damage_inv damage inv_this))))).
Admitted.

(*Why logic*) Definition Sword_tag : (tag_id Sword).
Admitted.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma attack_ensures_ok_po_1 : 
  forall (this: (pointer Hero)),
  forall (target: (pointer Hero)),
  forall (Hero_alloc_table: (alloc_table Hero)),
  forall (Hero_tag_table: (tag_table Hero)),
  forall (damage: (memory Sword Z)),
  forall (dead: (memory Hero bool)),
  forall (life: (memory Hero Z)),
  forall (sword: (memory Hero (pointer Sword))),
  forall (HW_1: ((((offset_min Hero_alloc_table this) <= 0 /\
                (offset_max Hero_alloc_table this) >= 0) /\
                (instanceof Hero_tag_table this Hero_tag)) /\
                ((offset_min Hero_alloc_table target) <= 0 /\
                (offset_max Hero_alloc_table target) >= 0) /\
                (instanceof Hero_tag_table target Hero_tag)) /\
                (Hero_inv this damage dead life sword) /\
                (Hero_inv target damage dead life sword)),
  (valid Hero_alloc_table target).
Admitted.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma attack_ensures_ok_po_2 : 
  forall (this: (pointer Hero)),
  forall (target: (pointer Hero)),
  forall (Hero_alloc_table: (alloc_table Hero)),
  forall (Hero_tag_table: (tag_table Hero)),
  forall (damage: (memory Sword Z)),
  forall (dead: (memory Hero bool)),
  forall (life: (memory Hero Z)),
  forall (sword: (memory Hero (pointer Sword))),
  forall (HW_1: ((((offset_min Hero_alloc_table this) <= 0 /\
                (offset_max Hero_alloc_table this) >= 0) /\
                (instanceof Hero_tag_table this Hero_tag)) /\
                ((offset_min Hero_alloc_table target) <= 0 /\
                (offset_max Hero_alloc_table target) >= 0) /\
                (instanceof Hero_tag_table target Hero_tag)) /\
                (Hero_inv this damage dead life sword) /\
                (Hero_inv target damage dead life sword)),
  forall (HW_2: (valid Hero_alloc_table target)),
  forall (result: Z),
  forall (HW_3: result = (select life target)),
  (valid Hero_alloc_table this).
Admitted.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma attack_ensures_ok_po_3 : 
  forall (this: (pointer Hero)),
  forall (target: (pointer Hero)),
  forall (Hero_alloc_table: (alloc_table Hero)),
  forall (Hero_tag_table: (tag_table Hero)),
  forall (Sword_alloc_table: (alloc_table Sword)),
  forall (damage: (memory Sword Z)),
  forall (dead: (memory Hero bool)),
  forall (life: (memory Hero Z)),
  forall (sword: (memory Hero (pointer Sword))),
  forall (HW_1: ((((offset_min Hero_alloc_table this) <= 0 /\
                (offset_max Hero_alloc_table this) >= 0) /\
                (instanceof Hero_tag_table this Hero_tag)) /\
                ((offset_min Hero_alloc_table target) <= 0 /\
                (offset_max Hero_alloc_table target) >= 0) /\
                (instanceof Hero_tag_table target Hero_tag)) /\
                (Hero_inv this damage dead life sword) /\
                (Hero_inv target damage dead life sword)),
  forall (HW_2: (valid Hero_alloc_table target)),
  forall (result: Z),
  forall (HW_3: result = (select life target)),
  forall (HW_4: (valid Hero_alloc_table this)),
  forall (result0: (pointer Sword)),
  forall (HW_5: result0 = (select sword this)),
  (valid Sword_alloc_table result0).
Admitted.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma attack_ensures_ok_po_4 : 
  forall (this: (pointer Hero)),
  forall (target: (pointer Hero)),
  forall (Hero_alloc_table: (alloc_table Hero)),
  forall (Hero_tag_table: (tag_table Hero)),
  forall (Sword_alloc_table: (alloc_table Sword)),
  forall (damage: (memory Sword Z)),
  forall (dead: (memory Hero bool)),
  forall (life: (memory Hero Z)),
  forall (sword: (memory Hero (pointer Sword))),
  forall (HW_1: ((((offset_min Hero_alloc_table this) <= 0 /\
                (offset_max Hero_alloc_table this) >= 0) /\
                (instanceof Hero_tag_table this Hero_tag)) /\
                ((offset_min Hero_alloc_table target) <= 0 /\
                (offset_max Hero_alloc_table target) >= 0) /\
                (instanceof Hero_tag_table target Hero_tag)) /\
                (Hero_inv this damage dead life sword) /\
                (Hero_inv target damage dead life sword)),
  forall (HW_2: (valid Hero_alloc_table target)),
  forall (result: Z),
  forall (HW_3: result = (select life target)),
  forall (HW_4: (valid Hero_alloc_table this)),
  forall (result0: (pointer Sword)),
  forall (HW_5: result0 = (select sword this)),
  forall (HW_6: (valid Sword_alloc_table result0)),
  forall (result1: Z),
  forall (HW_7: result1 = (select damage result0)),
  forall (HW_8: (valid Hero_alloc_table target)),
  forall (life0: (memory Hero Z)),
  forall (HW_9: life0 = (store life target (result - result1))),
  forall (HW_10: (valid Hero_alloc_table target)),
  forall (result2: Z),
  forall (HW_11: result2 = (select life0 target)),
  forall (HW_12: result2 <= 0),
  forall (HW_13: (valid Hero_alloc_table target)),
  forall (life1: (memory Hero Z)),
  forall (HW_14: life1 = (store life0 target 0)),
  forall (HW_15: (valid Hero_alloc_table target)),
  forall (dead0: (memory Hero bool)),
  forall (HW_16: dead0 = (store dead target true)),
  (Hero_inv this damage dead0 life1 sword).
Proof.
intros; subst.
clear HW_8 HW_10 HW_13 HW_15.
destruct HW_1 as [HW_1 H1].
destruct H1 as [H1 H2].
refine (proj2 (Hero_inv_sem _ _ _ _ _) _).
intro NN1.
assert (H3: Sword_inv (select sword this) damage).
refine (proj1 (proj1 (Hero_inv_sem _ _ _ _ _) _ _)); auto.
apply H1.
split; auto.
assert (H4: life_inv dead life this).
apply (proj2 (proj2 (proj1 (Hero_inv_sem sword life dead damage this)
  H1 NN1))).
assert (H5: this = target \/ this <> target).
apply eq_pointer.
destruct H5 as [H5 | H5].
rewrite <- H5 in *; clear H5 target.
set (new_life := select life this - select damage (select sword this)) in *.
unfold life_inv.
assert (H6: select (store (store life this new_life) this 0) this = 0).
apply select_store_eq; auto.
rewrite H6; clear H6.
split; try split; intuition.
apply (proj1 (proj2 (proj1 (Hero_inv_sem sword life dead damage this)
  H1 NN1))).
apply select_store_eq; auto.
set (new_life := select life target - select damage (select sword this)) in *.
split; auto.
apply (proj1 (proj2 (proj1 (Hero_inv_sem sword life dead damage this)
  H1 NN1))).
unfold life_inv.
assert (H6: select (store (store life target new_life) target 0) this =
  select (store life target new_life) this).
apply select_store_neq; auto.
rewrite H6 in *; clear H6.
assert (H6: select (store life target new_life) this = select life this).
apply select_store_neq; auto.
rewrite H6 in *; clear H6.
unfold life_inv in H4.
assert (H6: select (store dead target true) this = select dead this).
apply select_store_neq; auto.
rewrite H6 in *; clear H6.
destruct H4 as [H4 H6].
destruct H6 as [H6 H7].
split; try split; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma attack_ensures_ok_po_5 : 
  forall (this: (pointer Hero)),
  forall (target: (pointer Hero)),
  forall (Hero_alloc_table: (alloc_table Hero)),
  forall (Hero_tag_table: (tag_table Hero)),
  forall (Sword_alloc_table: (alloc_table Sword)),
  forall (damage: (memory Sword Z)),
  forall (dead: (memory Hero bool)),
  forall (life: (memory Hero Z)),
  forall (sword: (memory Hero (pointer Sword))),
  forall (HW_1: ((((offset_min Hero_alloc_table this) <= 0 /\
                (offset_max Hero_alloc_table this) >= 0) /\
                (instanceof Hero_tag_table this Hero_tag)) /\
                ((offset_min Hero_alloc_table target) <= 0 /\
                (offset_max Hero_alloc_table target) >= 0) /\
                (instanceof Hero_tag_table target Hero_tag)) /\
                (Hero_inv this damage dead life sword) /\
                (Hero_inv target damage dead life sword)),
  forall (HW_2: (valid Hero_alloc_table target)),
  forall (result: Z),
  forall (HW_3: result = (select life target)),
  forall (HW_4: (valid Hero_alloc_table this)),
  forall (result0: (pointer Sword)),
  forall (HW_5: result0 = (select sword this)),
  forall (HW_6: (valid Sword_alloc_table result0)),
  forall (result1: Z),
  forall (HW_7: result1 = (select damage result0)),
  forall (HW_8: (valid Hero_alloc_table target)),
  forall (life0: (memory Hero Z)),
  forall (HW_9: life0 = (store life target (result - result1))),
  forall (HW_10: (valid Hero_alloc_table target)),
  forall (result2: Z),
  forall (HW_11: result2 = (select life0 target)),
  forall (HW_12: result2 <= 0),
  forall (HW_13: (valid Hero_alloc_table target)),
  forall (life1: (memory Hero Z)),
  forall (HW_14: life1 = (store life0 target 0)),
  forall (HW_15: (valid Hero_alloc_table target)),
  forall (dead0: (memory Hero bool)),
  forall (HW_16: dead0 = (store dead target true)),
  (Hero_inv target damage dead0 life1 sword).
Proof.
intros; subst.
clear HW_8 HW_10 HW_13 HW_15.
destruct HW_1 as [HW_1 H1].
destruct H1 as [H1 H2].
refine (proj2 (Hero_inv_sem _ _ _ _ _) _).
intro NN1.
assert (H3: Sword_inv (select sword target) damage).
refine (proj1 (proj1 (Hero_inv_sem _ _ _ _ _) _ _)); auto.
apply H2.
split; auto.
assert (H4: life_inv dead life target).
apply (proj2 (proj2 (proj1 (Hero_inv_sem sword life dead damage target)
  H2 NN1))).
set (new_life := select life target - select damage (select sword this)).
assert (H5: select (store (store life target new_life) target 0) target = 0).
apply select_store_eq; auto.
split.
apply (proj1 (proj2 (proj1 (Hero_inv_sem sword life dead damage target)
  H2 NN1))).
unfold life_inv; repeat split; rewrite H5; try omega.
intro H; clear H.
apply select_store_eq; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma attack_ensures_ok_po_6 : 
  forall (this: (pointer Hero)),
  forall (target: (pointer Hero)),
  forall (Hero_alloc_table: (alloc_table Hero)),
  forall (Hero_tag_table: (tag_table Hero)),
  forall (Sword_alloc_table: (alloc_table Sword)),
  forall (damage: (memory Sword Z)),
  forall (dead: (memory Hero bool)),
  forall (life: (memory Hero Z)),
  forall (sword: (memory Hero (pointer Sword))),
  forall (HW_1: ((((offset_min Hero_alloc_table this) <= 0 /\
                (offset_max Hero_alloc_table this) >= 0) /\
                (instanceof Hero_tag_table this Hero_tag)) /\
                ((offset_min Hero_alloc_table target) <= 0 /\
                (offset_max Hero_alloc_table target) >= 0) /\
                (instanceof Hero_tag_table target Hero_tag)) /\
                (Hero_inv this damage dead life sword) /\
                (Hero_inv target damage dead life sword)),
  forall (HW_2: (valid Hero_alloc_table target)),
  forall (result: Z),
  forall (HW_3: result = (select life target)),
  forall (HW_4: (valid Hero_alloc_table this)),
  forall (result0: (pointer Sword)),
  forall (HW_5: result0 = (select sword this)),
  forall (HW_6: (valid Sword_alloc_table result0)),
  forall (result1: Z),
  forall (HW_7: result1 = (select damage result0)),
  forall (HW_8: (valid Hero_alloc_table target)),
  forall (life0: (memory Hero Z)),
  forall (HW_9: life0 = (store life target (result - result1))),
  forall (HW_10: (valid Hero_alloc_table target)),
  forall (result2: Z),
  forall (HW_11: result2 = (select life0 target)),
  forall (HW_17: result2 > 0),
  (Hero_inv this damage dead life0 sword).
Proof.
intros; subst.
clear HW_8 HW_10.
destruct HW_1 as [HW_1 H1].
destruct H1 as [H1 H2].
refine (proj2 (Hero_inv_sem _ _ _ _ _) _).
intro NN1.
assert (H3: Sword_inv (select sword this) damage).
refine (proj1 (proj1 (Hero_inv_sem _ _ _ _ _) _ _)); auto.
apply H1.
split; auto.
assert (H4: life_inv dead life this).
apply (proj2 (proj2 (proj1 (Hero_inv_sem sword life dead damage this)
  H1 NN1))).
assert (H7: this = target \/ this <> target).
apply eq_pointer.
destruct H7 as [H7 | H7].
rewrite <- H7 in *; clear H7 target.
set (new_life := select life this - select damage (select sword this)) in *.
assert (H5: select (store life this new_life) this = new_life).
apply select_store_eq; auto.
unfold life_inv.
rewrite H5 in *; clear H5.
unfold life_inv in H4.
destruct H4 as [H4 H5].
destruct H5 as [H5 H6].
assert (H7: select damage (select sword this) > 0).
refine (proj1 (Sword_inv_sem _ _) _ _); auto.
intro SN.
rewrite SN in HW_6.
assert (~valid Sword_alloc_table (null Sword)).
apply null_not_valid.
auto.
repeat split; try omega.
apply (proj1 (proj2 (proj1 (Hero_inv_sem sword life dead damage this)
  H1 NN1))).
unfold new_life.
omega.
intro H8.
rewrite H8 in HW_17.
assert (F: False).
apply (Zgt_irrefl 0); auto.
destruct F.
unfold life_inv.
set (new_life := select life target - select damage (select sword this)) in *.
assert (E: select (store life target new_life) this = select life this).
apply select_store_neq; auto.
rewrite E in *; clear E.
split.
apply (proj1 (proj2 (proj1 (Hero_inv_sem sword life dead damage this)
  H1 NN1))).
unfold life_inv in H4.
auto.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma attack_ensures_ok_po_7 : 
  forall (this: (pointer Hero)),
  forall (target: (pointer Hero)),
  forall (Hero_alloc_table: (alloc_table Hero)),
  forall (Hero_tag_table: (tag_table Hero)),
  forall (Sword_alloc_table: (alloc_table Sword)),
  forall (damage: (memory Sword Z)),
  forall (dead: (memory Hero bool)),
  forall (life: (memory Hero Z)),
  forall (sword: (memory Hero (pointer Sword))),
  forall (HW_1: ((((offset_min Hero_alloc_table this) <= 0 /\
                (offset_max Hero_alloc_table this) >= 0) /\
                (instanceof Hero_tag_table this Hero_tag)) /\
                ((offset_min Hero_alloc_table target) <= 0 /\
                (offset_max Hero_alloc_table target) >= 0) /\
                (instanceof Hero_tag_table target Hero_tag)) /\
                (Hero_inv this damage dead life sword) /\
                (Hero_inv target damage dead life sword)),
  forall (HW_2: (valid Hero_alloc_table target)),
  forall (result: Z),
  forall (HW_3: result = (select life target)),
  forall (HW_4: (valid Hero_alloc_table this)),
  forall (result0: (pointer Sword)),
  forall (HW_5: result0 = (select sword this)),
  forall (HW_6: (valid Sword_alloc_table result0)),
  forall (result1: Z),
  forall (HW_7: result1 = (select damage result0)),
  forall (HW_8: (valid Hero_alloc_table target)),
  forall (life0: (memory Hero Z)),
  forall (HW_9: life0 = (store life target (result - result1))),
  forall (HW_10: (valid Hero_alloc_table target)),
  forall (result2: Z),
  forall (HW_11: result2 = (select life0 target)),
  forall (HW_17: result2 > 0),
  (Hero_inv target damage dead life0 sword).
Proof.
intros; subst.
clear HW_8 HW_10.
destruct HW_1 as [HW_1 H1].
destruct H1 as [H1 H2].
refine (proj2 (Hero_inv_sem _ _ _ _ _) _).
intro NN1.
assert (H3: Sword_inv (select sword target) damage).
refine (proj1 (proj1 (Hero_inv_sem _ _ _ _ _) _ _)); auto.
apply H2.
split; auto.
assert (H4: life_inv dead life target).
apply (proj2 (proj2 (proj1 (Hero_inv_sem sword life dead damage target)
  H2 NN1))).
set (new_life := select life target - select damage (select sword this)) in *.
assert (H5: select (store life target new_life) target = new_life).
apply select_store_eq; auto.
rewrite H5 in HW_17.
assert (NN2: this <> null Hero).
assert (~valid Hero_alloc_table (null Hero)).
apply null_not_valid; auto.
intro E; rewrite E in *.
auto.
split.
refine (proj1 (proj2 (proj1 (Hero_inv_sem _ _ _ _ _) _ _))); auto.
apply H2.
unfold life_inv.
rewrite H5 in *.
repeat split; try omega.
assert (H7: select damage (select sword this) > 0).
refine (proj1 (Sword_inv_sem _ _) _ _); auto.
refine (proj1 (proj1 (Hero_inv_sem _ _ _ _ _) _ _)).
apply H1.
auto.
refine (proj1 (proj2 (proj1 (Hero_inv_sem _ _ _ _ _) _ _))); auto.
apply H1.
unfold life_inv in H4.
destruct H4 as [_ H4].
destruct H4 as [H4 _].
unfold new_life.
omega.
intro E; rewrite E in HW_17.
assert (F: False).
apply (Zgt_irrefl 0); auto.
destruct F.
Save.
