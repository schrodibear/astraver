(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export jessie_why.

(*Why type*) Definition Hero: Set.
Admitted.

(*Why type*) Definition Shield: Set.
Admitted.

(*Why type*) Definition Sword: Set.
Admitted.

(*Why logic*) Definition Hero_tag : (tag_id Hero).
Admitted.

(*Why axiom*) Lemma Hero_parenttag_bottom :
  (parenttag Hero_tag (@bottom_tag Hero)).
Admitted.

(*Why logic*) Definition Shield_tag : (tag_id Shield).
Admitted.

(*Why axiom*) Lemma Shield_parenttag_bottom :
  (parenttag Shield_tag (@bottom_tag Shield)).
Admitted.

(*Why logic*) Definition Sorcerer_tag : (tag_id Hero).
Admitted.

(*Why axiom*) Lemma Sorcerer_parenttag_Hero :
  (parenttag Sorcerer_tag Hero_tag).
Admitted.

(*Why logic*) Definition Sword_tag : (tag_id Sword).
Admitted.

(*Why axiom*) Lemma Sword_parenttag_bottom :
  (parenttag Sword_tag (@bottom_tag Sword)).
Admitted.

(*Why predicate*) Definition absorb_inv  (absorb:(memory Shield Z)) (this:(pointer Shield))
  := (select absorb this) >= 0.

(*Why predicate*) Definition life_inv  (dead:(memory Hero bool)) (life:(memory Hero Z)) (this:(pointer Hero))
  := (select life this) >= 0 /\ (select life this) <= 100 /\
     (((select life this) = 0 -> (select dead this) = true)).

(*Why predicate*) Definition damage_inv  (damage:(memory Sword Z)) (this:(pointer Sword))
  := (select damage this) > 0.

(*Why predicate*) Definition mana_inv  (mana:(memory Hero Z)) (this:(pointer Hero))
  := (select mana this) >= 0.

(*Why predicate*) Definition test  (sword:(memory Hero (pointer Sword))) (damage:(memory Sword Z)) (this:(pointer Hero))
  := (select damage (shift (select sword this) 4)) = 5.

(*Why predicate*) Definition sword_inv  (Sword_alloc_table:(alloc_table Sword)) (sword:(memory Hero (pointer Sword))) (this:(pointer Hero))
  := (offset_min Sword_alloc_table (select sword this)) <= 0 /\
     (offset_max Sword_alloc_table (select sword this)) >= 0.

(*Why predicate*) Definition global_invariant_Hero  (Hero_alloc_table:(alloc_table Hero)) (Hero_tag_table:(tag_table Hero)) (Shield_alloc_table:(alloc_table Shield)) (Sword_alloc_table:(alloc_table Sword)) (committed_Hero:(memory Hero bool)) (committed_Shield:(memory Shield bool)) (committed_Sword:(memory Sword bool)) (damage:(memory Sword Z)) (dead:(memory Hero bool)) (life:(memory Hero Z)) (mana:(memory Hero Z)) (mutable_Hero:(memory Hero (tag_id Hero))) (shield:(memory Hero (pointer Shield))) (sword:(memory Hero (pointer Sword)))
  := (forall (this:(pointer Hero)),
      ((((subtag (select mutable_Hero this) Sorcerer_tag) ->
         (mana_inv mana this))) /\
      (((subtag (select mutable_Hero this) Hero_tag) ->
        (test sword damage this))) /\
      (((subtag (select mutable_Hero this) Hero_tag) ->
        (sword_inv Sword_alloc_table sword this))) /\
      (((subtag (select mutable_Hero this) Hero_tag) ->
        (life_inv dead life this)))) /\
      ((((subtag (select mutable_Hero this) Hero_tag) ->
         (forall (jc_index:Z),
          (jc_index = 0 ->
           (select committed_Shield (shift (select shield this) jc_index)) =
           true)) /\
         (forall (jc_index:Z),
          (jc_index = 0 ->
           (select committed_Sword (shift (select sword this) jc_index)) =
           true)))) /\
      (((subtag (select mutable_Hero this) Sorcerer_tag) -> True))) /\
      (((select committed_Hero this) = true ->
        (fully_packed Hero_tag_table mutable_Hero this))) /\
      (forall (jc_index:Z),
       (forall (jc_index_2:Z),
        (forall (this_2:(pointer Hero)),
         (jc_index = 0 /\ jc_index_2 = 0 /\
          (shift (select sword this) jc_index) =
          (shift (select sword this) jc_index_2) /\
          (select committed_Sword (shift (select sword this) jc_index)) =
          true \/ jc_index = 0 /\ jc_index_2 = 0 /\
          (shift (select shield this) jc_index) =
          (shift (select shield this) jc_index_2) /\
          (select committed_Shield (shift (select shield this) jc_index)) =
          true -> this = this_2))))).

(*Why predicate*) Definition global_invariant_Shield  (Shield_alloc_table:(alloc_table Shield)) (Shield_tag_table:(tag_table Shield)) (absorb:(memory Shield Z)) (committed_Shield:(memory Shield bool)) (mutable_Shield:(memory Shield (tag_id Shield)))
  := (forall (this:(pointer Shield)),
      (((subtag (select mutable_Shield this) Shield_tag) ->
        (absorb_inv absorb this))) /\
      (((subtag (select mutable_Shield this) Shield_tag) -> True)) /\
      (((select committed_Shield this) = true ->
        (fully_packed Shield_tag_table mutable_Shield this))) /\
      (forall (jc_index:Z),
       (forall (jc_index_2:Z),
        (forall (this_2:(pointer Shield)), (False -> this = this_2))))).

(*Why predicate*) Definition global_invariant_Sword  (Sword_alloc_table:(alloc_table Sword)) (Sword_tag_table:(tag_table Sword)) (committed_Sword:(memory Sword bool)) (damage:(memory Sword Z)) (mutable_Sword:(memory Sword (tag_id Sword)))
  := (forall (this:(pointer Sword)),
      (((subtag (select mutable_Sword this) Sword_tag) ->
        (damage_inv damage this))) /\
      (((subtag (select mutable_Sword this) Sword_tag) -> True)) /\
      (((select committed_Sword this) = true ->
        (fully_packed Sword_tag_table mutable_Sword this))) /\
      (forall (jc_index:Z),
       (forall (jc_index_2:Z),
        (forall (this_2:(pointer Sword)), (False -> this = this_2))))).

(* Why obligation from file "", line 0, characters -1--1: *)
(*Why goal*) Lemma attack_safety_po_3 : 
  forall (this: (pointer Hero)),
  forall (target: (pointer Hero)),
  forall (Hero_alloc_table: (alloc_table Hero)),
  forall (Hero_tag_table: (tag_table Hero)),
  forall (Shield_alloc_table: (alloc_table Shield)),
  forall (Shield_tag_table: (tag_table Shield)),
  forall (Sword_alloc_table: (alloc_table Sword)),
  forall (Sword_tag_table: (tag_table Sword)),
  forall (absorb: (memory Shield Z)),
  forall (committed_Hero: (memory Hero bool)),
  forall (committed_Shield: (memory Shield bool)),
  forall (committed_Sword: (memory Sword bool)),
  forall (damage: (memory Sword Z)),
  forall (dead: (memory Hero bool)),
  forall (life: (memory Hero Z)),
  forall (mana: (memory Hero Z)),
  forall (mutable_Hero: (memory Hero (tag_id Hero))),
  forall (mutable_Shield: (memory Shield (tag_id Shield))),
  forall (mutable_Sword: (memory Sword (tag_id Sword))),
  forall (shield: (memory Hero (pointer Shield))),
  forall (sword: (memory Hero (pointer Sword))),
  forall (HW_1: (((offset_min Hero_alloc_table this) <= 0 /\
                (offset_max Hero_alloc_table this) >= 0) /\
                (instanceof Hero_tag_table this Hero_tag)) /\
                (((offset_min Hero_alloc_table target) <= 0 /\
                (offset_max Hero_alloc_table target) >= 0) /\
                (instanceof Hero_tag_table target Hero_tag)) /\
                (* JC_1 *) ((select mutable_Hero this) = Hero_tag /\
                (select mutable_Hero target) = Hero_tag /\
                (select committed_Hero target) = false)),
  forall (HW_2: (global_invariant_Hero
                 Hero_alloc_table Hero_tag_table Shield_alloc_table Sword_alloc_table committed_Hero committed_Shield committed_Sword damage dead life mana mutable_Hero shield sword)),
  forall (HW_3: (global_invariant_Shield
                 Shield_alloc_table Shield_tag_table absorb committed_Shield mutable_Shield)),
  forall (HW_4: (global_invariant_Sword
                 Sword_alloc_table Sword_tag_table committed_Sword damage mutable_Sword)),
  forall (HW_5: (parenttag (select mutable_Hero target) (@bottom_tag Hero)) /\
                false = (select committed_Hero target)),
  forall (committed_Shield0: (memory Shield bool)),
  forall (committed_Sword0: (memory Sword bool)),
  forall (mutable_Hero0: (memory Hero (tag_id Hero))),
  forall (HW_6: mutable_Hero0 =
                (store mutable_Hero target (@bottom_tag Hero)) /\
                ((not_assigns
                  Shield_alloc_table committed_Shield committed_Shield0 (
                  pset_range (pset_singleton (select shield target)) 0 0)) /\
                (forall (jc_index:Z),
                 (jc_index = 0 ->
                  (select
                   committed_Shield0 (shift (select shield target) jc_index)) =
                  false))) /\
                (not_assigns
                 Sword_alloc_table committed_Sword committed_Sword0 (
                 pset_range (pset_singleton (select sword target)) 0 0)) /\
                (forall (jc_index:Z),
                 (jc_index = 0 ->
                  (select
                   committed_Sword0 (shift (select sword target) jc_index)) =
                  false))),
  forall (result: Z),
  forall (HW_7: result = (select life target)),
  forall (result0: (pointer Sword)),
  forall (HW_8: result0 = (select sword this)),
  forall (result1: Z),
  forall (HW_9: result1 = (select damage result0)),
  forall (HW_10: (subtag (@bottom_tag Hero) (select mutable_Hero0 target))),
  forall (life0: (memory Hero Z)),
  forall (HW_11: life0 = (store life target (result - result1))),
  forall (HW_12: (global_invariant_Hero
                  Hero_alloc_table Hero_tag_table Shield_alloc_table Sword_alloc_table committed_Hero committed_Shield0 committed_Sword0 damage dead life0 mana mutable_Hero0 shield sword)),
  forall (result2: Z),
  forall (HW_13: result2 = (select life0 target)),
  forall (HW_14: result2 <= 0),
  forall (HW_15: (subtag (@bottom_tag Hero) (select mutable_Hero0 target))),
  forall (life1: (memory Hero Z)),
  forall (HW_16: life1 = (store life0 target 0)),
  forall (HW_17: (global_invariant_Hero
                  Hero_alloc_table Hero_tag_table Shield_alloc_table Sword_alloc_table committed_Hero committed_Shield0 committed_Sword0 damage dead life1 mana mutable_Hero0 shield sword)),
  forall (HW_18: (subtag (@bottom_tag Hero) (select mutable_Hero0 target))),
  forall (dead0: (memory Hero bool)),
  forall (HW_19: dead0 = (store dead target true)),
  forall (HW_20: (global_invariant_Hero
                  Hero_alloc_table Hero_tag_table Shield_alloc_table Sword_alloc_table committed_Hero committed_Shield0 committed_Sword0 damage dead0 life1 mana mutable_Hero0 shield sword)),
  ((parenttag Hero_tag (select mutable_Hero0 target)) /\
  ((test sword damage target) /\
  (sword_inv Sword_alloc_table sword target) /\
  (life_inv dead0 life1 target)) /\
  (forall (jc_index:Z),
   (jc_index = 0 ->
    (fully_packed
     Sword_tag_table mutable_Sword (shift (select sword target) jc_index)) /\
    (select committed_Sword0 (shift (select sword target) jc_index)) = false)) /\
  (forall (jc_index:Z),
   (jc_index = 0 ->
    (fully_packed
     Shield_tag_table mutable_Shield (shift (select shield target) jc_index)) /\
    (select committed_Shield0 (shift (select shield target) jc_index)) =
    false))).
Proof.
intros; subst.
split.
admit.
split.
admit.
split.
admit.
intros; subst.
assert (S: forall P Q, P /\ Q -> Q /\ P).
intuition.
apply S; clear S.
split.
admit.
(* let's prove "fully packed" *)
(* target.shield is fully packed because:
- it was fully packed before the "unpack" (HW_2..5?)
- and because its field "mutable" hasn't been changed (same variable) *)
(* first, let's clean things up a bit *)
clear HW_14 HW_20 HW_17 HW_12 HW_18 HW_15 HW_10.
clear HW_6 committed_Sword0 committed_Shield0 mutable_Hero0.
clear HW_4 HW_5.
(* applying global invariant correctly *)
apply (proj1 (proj2 (proj2 (HW_3 (shift (select shield target) 0))))).
clear HW_3.
(* the Shield is committed because the Hero is not mutable *)
refine (proj1 (proj1 (proj1 (proj2 (HW_2 target))) _) _ _).
destruct HW_1 as [_ [_ [_ [MV _]]]].
rewrite MV.
apply subtag_refl.
trivial.
Save.