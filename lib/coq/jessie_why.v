(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)
Require Export Why.

(*Why logic*) Definition bool_and : bool -> bool -> bool.
Admitted.

(*Why logic*) Definition bool_or : bool -> bool -> bool.
Admitted.

(*Why logic*) Definition bool_xor : bool -> bool -> bool.
Admitted.

(*Why axiom*) Lemma bool_and_false :
  (forall (b:bool), (bool_and b false) = false).
Admitted.

(*Why axiom*) Lemma false_bool_and :
  (forall (b:bool), (bool_and false b) = false).
Admitted.

(*Why axiom*) Lemma bool_and_true : (forall (b:bool), (bool_and b true) = b).
Admitted.

(*Why axiom*) Lemma true_bool_and : (forall (b:bool), (bool_and true b) = b).
Admitted.

(*Why axiom*) Lemma bool_and_1 :
  (forall (b1:bool),
   (forall (b2:bool), ((bool_and b1 b2) = true -> b1 = true /\ b2 = true))).
Admitted.

(*Why axiom*) Lemma div_positive_by_positive :
  (forall (a:Z),
   (forall (b:Z), (0 <= a /\ 0 < b -> 0 <= ((Zdiv a b)) /\ ((Zdiv a b)) <= a))).
Admitted.

(*Why axiom*) Lemma div_negative_by_positive :
  (forall (a:Z),
   (forall (b:Z), (a <= 0 /\ 0 < b -> a <= ((Zdiv a b)) /\ ((Zdiv a b)) <= 0))).
Admitted.

(*Why axiom*) Lemma div_positive_by_negative :
  (forall (a:Z),
   (forall (b:Z),
    (0 <= a /\ b < 0 -> (Zopp a) <= ((Zdiv a b)) /\ ((Zdiv a b)) <= 0))).
Admitted.

(*Why axiom*) Lemma div_negative_by_negative :
  (forall (a:Z),
   (forall (b:Z),
    (a <= 0 /\ b < 0 -> 0 <= ((Zdiv a b)) /\ ((Zdiv a b)) <= (Zopp a)))).
Admitted.

(*Why axiom*) Lemma mod_positive_by_positive :
  (forall (a:Z),
   (forall (b:Z), (0 <= a /\ 0 < b -> 0 <= ((Zmod a b)) /\ ((Zmod a b)) < b))).
Admitted.

(*Why axiom*) Lemma mod_negative_by_positive :
  (forall (a:Z),
   (forall (b:Z), (a <= 0 /\ 0 < b -> 0 <= ((Zmod a b)) /\ ((Zmod a b)) < b))).
Admitted.

(*Why axiom*) Lemma mod_positive_by_negative :
  (forall (a:Z),
   (forall (b:Z),
    (0 <= a /\ b < 0 -> (Zopp b) < ((Zmod a b)) /\ ((Zmod a b)) <= 0))).
Admitted.

(*Why axiom*) Lemma mod_negative_by_negative :
  (forall (a:Z),
   (forall (b:Z),
    (a <= 0 /\ b < 0 -> (Zopp b) < ((Zmod a b)) /\ ((Zmod a b)) <= 0))).
Admitted.

(*Why type*) Definition alloc_table: Set ->Set.
Admitted.

(*Why type*) Definition pointer: Set ->Set.
Admitted.

(*Why logic*) Definition offset_max :
  forall (A1:Set), (alloc_table A1) -> (pointer A1) -> Z.
Admitted.
Implicit Arguments offset_max.

(*Why logic*) Definition offset_min :
  forall (A1:Set), (alloc_table A1) -> (pointer A1) -> Z.
Admitted.
Implicit Arguments offset_min.

(*Why predicate*) Definition valid (A580:Set) (a:(alloc_table A580)) (p:(pointer A580))
  := (offset_min a p) <= 0 /\ (offset_max a p) >= 0.
Implicit Arguments valid.

(*Why logic*) Definition shift :
  forall (A1:Set), (pointer A1) -> Z -> (pointer A1).
Admitted.
Implicit Arguments shift.

(*Why logic*) Definition sub_pointer :
  forall (A1:Set), (pointer A1) -> (pointer A1) -> Z.
Admitted.
Implicit Arguments sub_pointer.

(*Why axiom*) Lemma shift_zero :
  forall (A1:Set), (forall (p:(pointer A1)), (shift p 0) = p).
Admitted.

(*Why axiom*) Lemma shift_shift :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (i:Z), (forall (j:Z), (shift (shift p i) j) = (shift p (i + j))))).
Admitted.

(*Why axiom*) Lemma offset_max_shift :
  forall (A1:Set),
  (forall (a:(alloc_table A1)),
   (forall (p:(pointer A1)),
    (forall (i:Z), (offset_max a (shift p i)) = ((offset_max a p) - i)))).
Admitted.

(*Why axiom*) Lemma offset_min_shift :
  forall (A1:Set),
  (forall (a:(alloc_table A1)),
   (forall (p:(pointer A1)),
    (forall (i:Z), (offset_min a (shift p i)) = ((offset_min a p) - i)))).
Admitted.

(*Why axiom*) Lemma neq_shift :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (i:Z), (forall (j:Z), (i <> j -> ~((shift p i) = (shift p j)))))).
Admitted.

(*Why logic*) Definition null : forall (A1:Set), (pointer A1).
Admitted.
Set Contextual Implicit.
Implicit Arguments null.
Unset Contextual Implicit.

(*Why axiom*) Lemma null_not_valid :
  forall (A1:Set), (forall (a:(alloc_table A1)), ~(valid a (@null A1))).
Admitted.

(*Why axiom*) Lemma null_pointer :
  forall (A1:Set),
  (forall (a:(alloc_table A1)), (offset_min a (@null A1)) <= 0 /\
   (offset_max a (@null A1)) <= (Zopp 2)).
Admitted.

(*Why logic*) Definition eq_pointer_bool :
  forall (A1:Set), (pointer A1) -> (pointer A1) -> bool.
Admitted.
Implicit Arguments eq_pointer_bool.

(*Why logic*) Definition neq_pointer_bool :
  forall (A1:Set), (pointer A1) -> (pointer A1) -> bool.
Admitted.
Implicit Arguments neq_pointer_bool.

(*Why axiom*) Lemma eq_pointer_bool_def :
  forall (A1:Set),
  (forall (p1:(pointer A1)),
   (forall (p2:(pointer A1)), ((eq_pointer_bool p1 p2) = true <-> p1 = p2))).
Admitted.

(*Why axiom*) Lemma neq_pointer_bool_def :
  forall (A1:Set),
  (forall (p1:(pointer A1)),
   (forall (p2:(pointer A1)),
    ((neq_pointer_bool p1 p2) = true <-> ~(p1 = p2)))).
Admitted.

(*Why axiom*) Lemma sub_pointer_shift :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)), p = (shift q (sub_pointer p q)))).
Admitted.

(*Why axiom*) Lemma sub_pointer_self :
  forall (A1:Set), (forall (p:(pointer A1)), (sub_pointer p p) = 0).
Admitted.

(*Why axiom*) Lemma sub_pointer_zero :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)), ((sub_pointer p q) = 0 -> p = q))).
Admitted.

(*Why axiom*) Lemma sub_pointer_shift_left :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)),
    (forall (i:Z), (sub_pointer (shift p i) q) = ((sub_pointer p q) + i)))).
Admitted.

(*Why axiom*) Lemma sub_pointer_shift_right :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)),
    (forall (i:Z), (sub_pointer p (shift q i)) = ((sub_pointer p q) - i)))).
Admitted.

(*Why type*) Definition memory: Set -> Set ->Set.
Admitted.

(*Why logic*) Definition select :
  forall (A1:Set), forall (A2:Set), (memory A2 A1) -> (pointer A2) -> A1.
Admitted.
Implicit Arguments select.

(*Why logic*) Definition store :
  forall (A1:Set), forall (A2:Set), (memory A1 A2) -> (pointer A1)
  -> A2 -> (memory A1 A2).
Admitted.
Implicit Arguments store.

(*Why axiom*) Lemma select_store_eq :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(memory A1 A2)),
   (forall (p1:(pointer A1)),
    (forall (p2:(pointer A1)),
     (forall (a:A2), (p1 = p2 -> (select (store m p1 a) p2) = a))))).
Admitted.

(*Why axiom*) Lemma select_store_neq :
  forall (A1:Set), forall (A2:Set),
  (forall (m:(memory A1 A2)),
   (forall (p1:(pointer A1)),
    (forall (p2:(pointer A1)),
     (forall (a:A2),
      (~(p1 = p2) -> (select (store m p1 a) p2) = (select m p2)))))).
Admitted.

(*Why type*) Definition pset: Set ->Set.
Admitted.

(*Why logic*) Definition pset_empty : forall (A1:Set), (pset A1).
Admitted.
Set Contextual Implicit.
Implicit Arguments pset_empty.
Unset Contextual Implicit.

(*Why logic*) Definition pset_singleton :
  forall (A1:Set), (pointer A1) -> (pset A1).
Admitted.
Implicit Arguments pset_singleton.

(*Why logic*) Definition pset_deref :
  forall (A1:Set), forall (A2:Set), (memory A2 (pointer A1))
  -> (pset A2) -> (pset A1).
Admitted.
Implicit Arguments pset_deref.

(*Why logic*) Definition pset_union :
  forall (A1:Set), (pset A1) -> (pset A1) -> (pset A1).
Admitted.
Implicit Arguments pset_union.

(*Why logic*) Definition pset_all : forall (A1:Set), (pset A1) -> (pset A1).
Admitted.
Implicit Arguments pset_all.

(*Why logic*) Definition pset_range :
  forall (A1:Set), (pset A1) -> Z -> Z -> (pset A1).
Admitted.
Implicit Arguments pset_range.

(*Why logic*) Definition pset_range_left :
  forall (A1:Set), (pset A1) -> Z -> (pset A1).
Admitted.
Implicit Arguments pset_range_left.

(*Why logic*) Definition pset_range_right :
  forall (A1:Set), (pset A1) -> Z -> (pset A1).
Admitted.
Implicit Arguments pset_range_right.

(*Why logic*) Definition in_pset :
  forall (A1:Set), (pointer A1) -> (pset A1) -> Prop.
Admitted.
Implicit Arguments in_pset.

(*Why logic*) Definition valid_pset :
  forall (A1:Set), (alloc_table A1) -> (pset A1) -> Prop.
Admitted.
Implicit Arguments valid_pset.

(*Why predicate*) Definition pset_disjoint (A619:Set) (ps1:(pset A619)) (ps2:(pset A619))
  := (forall (p:(pointer A619)), ~((in_pset p ps1) /\ (in_pset p ps2))).
Implicit Arguments pset_disjoint.

(*Why axiom*) Lemma in_pset_empty :
  forall (A1:Set), (forall (p:(pointer A1)), ~(in_pset p (@pset_empty A1))).
Admitted.

(*Why axiom*) Lemma in_pset_singleton :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)), ((in_pset p (pset_singleton q)) <-> p = q))).
Admitted.

(*Why axiom*) Lemma in_pset_deref :
  forall (A1:Set), forall (A2:Set),
  (forall (p:(pointer A1)),
   (forall (m:(memory A2 (pointer A1))),
    (forall (q:(pset A2)),
     ((in_pset p (pset_deref m q)) <->
      (exists r:(pointer A2), (in_pset r q) /\ p = (select m r)))))).
Admitted.

(*Why axiom*) Lemma in_pset_all :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pset A1)),
    ((in_pset p (pset_all q)) <->
     (exists i:Z, (exists r:(pointer A1), (in_pset r q) /\ p = (shift r i)))))).
Admitted.

(*Why axiom*) Lemma in_pset_range :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pset A1)),
    (forall (a:Z),
     (forall (b:Z),
      ((in_pset p (pset_range q a b)) <->
       (exists i:Z,
        (exists r:(pointer A1), a <= i /\ i <= b /\ (in_pset r q) /\
         p = (shift r i)))))))).
Admitted.

(*Why axiom*) Lemma in_pset_range_left :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pset A1)),
    (forall (b:Z),
     ((in_pset p (pset_range_left q b)) <->
      (exists i:Z,
       (exists r:(pointer A1), i <= b /\ (in_pset r q) /\ p = (shift r i))))))).
Admitted.

(*Why axiom*) Lemma in_pset_range_right :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pset A1)),
    (forall (a:Z),
     ((in_pset p (pset_range_right q a)) <->
      (exists i:Z,
       (exists r:(pointer A1), a <= i /\ (in_pset r q) /\ p = (shift r i))))))).
Admitted.

(*Why axiom*) Lemma in_pset_union :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (s1:(pset A1)),
    (forall (s2:(pset A1)),
     ((in_pset p (pset_union s1 s2)) <-> (in_pset p s1) \/ (in_pset p s2))))).
Admitted.

(*Why axiom*) Lemma valid_pset_empty :
  forall (A1:Set),
  (forall (a:(alloc_table A1)), (valid_pset a (@pset_empty A1))).
Admitted.

(*Why axiom*) Lemma valid_pset_singleton :
  forall (A1:Set),
  (forall (a:(alloc_table A1)),
   (forall (p:(pointer A1)),
    ((valid_pset a (pset_singleton p)) <-> (valid a p)))).
Admitted.

(*Why axiom*) Lemma valid_pset_deref :
  forall (A1:Set), forall (A2:Set),
  (forall (a:(alloc_table A1)),
   (forall (m:(memory A2 (pointer A1))),
    (forall (q:(pset A2)),
     ((valid_pset a (pset_deref m q)) <->
      (forall (r:(pointer A2)),
       (forall (p:(pointer A1)),
        ((in_pset r q) /\ p = (select m r) -> (valid a p)))))))).
Admitted.

(*Why axiom*) Lemma valid_pset_range :
  forall (A1:Set),
  (forall (a:(alloc_table A1)),
   (forall (q:(pset A1)),
    (forall (c:Z),
     (forall (d:Z),
      ((valid_pset a (pset_range q c d)) <->
       (forall (i:Z),
        (forall (r:(pointer A1)),
         ((in_pset r q) /\ c <= i /\ i <= d -> (valid a (shift r i)))))))))).
Admitted.

(*Why axiom*) Lemma valid_pset_union :
  forall (A1:Set),
  (forall (a:(alloc_table A1)),
   (forall (s1:(pset A1)),
    (forall (s2:(pset A1)),
     ((valid_pset a (pset_union s1 s2)) <-> (valid_pset a s1) /\
      (valid_pset a s2))))).
Admitted.

(*Why predicate*) Definition not_assigns (A636:Set) (A635:Set) (a:(alloc_table A635)) (m1:(memory A635 A636)) (m2:(memory A635 A636)) (l:(pset A635))
  := (forall (p:(pointer A635)),
      ((valid a p) /\ ~(in_pset p l) -> (select m2 p) = (select m1 p))).
Implicit Arguments not_assigns.

(*Why axiom*) Lemma not_assigns_refl :
  forall (A1:Set), forall (A2:Set),
  (forall (a:(alloc_table A1)),
   (forall (m:(memory A1 A2)), (forall (l:(pset A1)), (not_assigns a m m l)))).
Admitted.

(*Why axiom*) Lemma not_assigns_trans :
  forall (A1:Set), forall (A2:Set),
  (forall (a:(alloc_table A1)),
   (forall (m1:(memory A1 A2)),
    (forall (m2:(memory A1 A2)),
     (forall (m3:(memory A1 A2)),
      (forall (l:(pset A1)),
       ((not_assigns a m1 m2 l) ->
        ((not_assigns a m2 m3 l) -> (not_assigns a m1 m3 l)))))))).
Admitted.

(*Why logic*) Definition full_separated :
  forall (A1:Set), forall (A2:Set), (pointer A1) -> (pointer A2) -> Prop.
Admitted.
Implicit Arguments full_separated.

(*Why axiom*) Lemma full_separated_shift1 :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)),
    (forall (i:Z), ((full_separated p q) -> (full_separated p (shift q i)))))).
Admitted.

(*Why axiom*) Lemma full_separated_shift2 :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)),
    (forall (i:Z), ((full_separated p q) -> (full_separated (shift q i) p))))).
Admitted.

(*Why axiom*) Lemma full_separated_shift3 :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)),
    (forall (i:Z), ((full_separated q p) -> (full_separated (shift q i) p))))).
Admitted.

(*Why axiom*) Lemma full_separated_shift4 :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)),
    (forall (i:Z), ((full_separated q p) -> (full_separated p (shift q i)))))).
Admitted.

(*Why type*) Definition tag_table: Set ->Set.
Admitted.

(*Why type*) Definition tag_id: Set ->Set.
Admitted.

(*Why logic*) Definition int_of_tag : forall (A1:Set), (tag_id A1) -> Z.
Admitted.
Implicit Arguments int_of_tag.

(*Why logic*) Definition typeof :
  forall (A1:Set), (tag_table A1) -> (pointer A1) -> (tag_id A1).
Admitted.
Implicit Arguments typeof.

(*Why logic*) Definition parenttag :
  forall (A1:Set), (tag_id A1) -> (tag_id A1) -> Prop.
Admitted.
Implicit Arguments parenttag.

(*Why logic*) Definition subtag :
  forall (A1:Set), (tag_id A1) -> (tag_id A1) -> Prop.
Admitted.
Implicit Arguments subtag.

(*Why logic*) Definition subtag_bool :
  forall (A1:Set), (tag_id A1) -> (tag_id A1) -> bool.
Admitted.
Implicit Arguments subtag_bool.

(*Why axiom*) Lemma subtag_bool_def :
  forall (A1:Set),
  (forall (t1:(tag_id A1)),
   (forall (t2:(tag_id A1)), ((subtag_bool t1 t2) = true <-> (subtag t1 t2)))).
Admitted.

(*Why axiom*) Lemma subtag_refl :
  forall (A1:Set), (forall (t:(tag_id A1)), (subtag t t)).
Admitted.

(*Why axiom*) Lemma subtag_parent :
  forall (A1:Set),
  (forall (t1:(tag_id A1)),
   (forall (t2:(tag_id A1)),
    (forall (t3:(tag_id A1)),
     ((subtag t1 t2) -> ((parenttag t2 t3) -> (subtag t1 t3)))))).
Admitted.

(*Why predicate*) Definition instanceof (A655:Set) (a:(tag_table A655)) (p:(pointer A655)) (t:(tag_id A655))
  := (subtag (typeof a p) t).
Implicit Arguments instanceof.

(*Why logic*) Definition downcast :
  forall (A1:Set), (tag_table A1) -> (pointer A1)
  -> (tag_id A1) -> (pointer A1).
Admitted.
Implicit Arguments downcast.

(*Why axiom*) Lemma downcast_instanceof :
  forall (A1:Set),
  (forall (a:(tag_table A1)),
   (forall (p:(pointer A1)),
    (forall (s:(tag_id A1)), ((instanceof a p s) -> (downcast a p s) = p)))).
Admitted.

(*Why logic*) Definition bottom_tag : forall (A1:Set), (tag_id A1).
Admitted.
Set Contextual Implicit.
Implicit Arguments bottom_tag.
Unset Contextual Implicit.

(*Why axiom*) Lemma bottom_tag_axiom :
  forall (A1:Set), (forall (t:(tag_id A1)), (subtag t (@bottom_tag A1))).
Admitted.

(*Why predicate*) Definition root_tag (A660:Set) (t:(tag_id A660))
  := (parenttag t (@bottom_tag A660)).
Implicit Arguments root_tag.

(*Why axiom*) Lemma root_subtag :
  forall (A1:Set),
  (forall (a:(tag_id A1)),
   (forall (b:(tag_id A1)),
    (forall (c:(tag_id A1)),
     ((root_tag a) ->
      ((root_tag b) -> (~(a = b) -> ((subtag c a) -> ~(subtag c b)))))))).
Admitted.

(*Why predicate*) Definition fully_packed (A662:Set) (tag_table:(tag_table A662)) (mutable:(memory A662 (tag_id A662))) (this:(pointer A662))
  := (select mutable this) = (typeof tag_table this).
Implicit Arguments fully_packed.

(*Why logic*) Definition bw_compl : Z -> Z.
Admitted.

(*Why logic*) Definition bw_and : Z -> Z -> Z.
Admitted.

(*Why axiom*) Lemma bw_and_not_null :
  (forall (a:Z), (forall (b:Z), ((bw_and a b) <> 0 -> a <> 0 /\ b <> 0))).
Admitted.

(*Why logic*) Definition bw_xor : Z -> Z -> Z.
Admitted.

(*Why logic*) Definition bw_or : Z -> Z -> Z.
Admitted.

(*Why logic*) Definition lsl : Z -> Z -> Z.
Admitted.

(*Why axiom*) Lemma lsl_left_positive_returns_positive :
  (forall (a:Z), (forall (b:Z), (0 <= a /\ 0 <= b -> 0 <= (lsl a b)))).
Admitted.

(*Why axiom*) Lemma lsl_left_positive_monotone :
  (forall (a1:Z),
   (forall (a2:Z),
    (forall (b:Z),
     (0 <= a1 /\ a1 <= a2 /\ 0 <= b -> (lsl a1 b) <= (lsl a2 b))))).
Admitted.

(*Why logic*) Definition lsr : Z -> Z -> Z.
Admitted.

(*Why axiom*) Lemma lsr_left_positive_returns_positive :
  (forall (a:Z), (forall (b:Z), (0 <= a /\ 0 <= b -> 0 <= (lsr a b)))).
Admitted.

(*Why axiom*) Lemma lsr_left_positive_decreases :
  (forall (a:Z), (forall (b:Z), (0 <= a /\ 0 <= b -> (lsr a b) <= a))).
Admitted.

(*Why logic*) Definition asr : Z -> Z -> Z.
Admitted.

(*Why axiom*) Lemma asr_positive_on_positive :
  (forall (a:Z), (forall (b:Z), (0 <= a /\ 0 <= b -> 0 <= (asr a b)))).
Admitted.

(*Why axiom*) Lemma asr_decreases_on_positive :
  (forall (a:Z), (forall (b:Z), (0 <= a /\ 0 <= b -> (asr a b) <= a))).
Admitted.

(*Why axiom*) Lemma asr_lsr_same_on_positive :
  (forall (a:Z), (forall (b:Z), (0 <= a /\ 0 <= b -> (asr a b) = (lsr a b)))).
Admitted.

(*Why axiom*) Lemma lsl_of_lsr_decreases_on_positive :
  (forall (a:Z), (forall (b:Z), (0 <= a /\ 0 <= b -> (lsl (lsr a b) b) <= a))).
Admitted.

(*Why axiom*) Lemma lsr_of_lsl_identity_on_positive :
  (forall (a:Z), (forall (b:Z), (0 <= a /\ 0 <= b -> (lsr (lsl a b) b) = a))).
Admitted.

(*Why logic*) Definition alloc_extends :
  forall (A1:Set), (alloc_table A1) -> (alloc_table A1) -> Prop.
Admitted.
Implicit Arguments alloc_extends.

(*Why logic*) Definition alloc_extern :
  forall (A1:Set), (alloc_table A1) -> (pointer A1) -> Prop.
Admitted.
Implicit Arguments alloc_extern.

(*Why axiom*) Lemma alloc_extends_offset_min :
  forall (A1:Set),
  (forall (a1:(alloc_table A1)),
   (forall (a2:(alloc_table A1)),
    ((alloc_extends a1 a2) ->
     (forall (p:(pointer A1)), (offset_min a1 p) = (offset_min a2 p))))).
Admitted.

(*Why axiom*) Lemma alloc_extends_offset_max :
  forall (A1:Set),
  (forall (a1:(alloc_table A1)),
   (forall (a2:(alloc_table A1)),
    ((alloc_extends a1 a2) ->
     (forall (p:(pointer A1)), (offset_max a1 p) = (offset_max a2 p))))).
Admitted.

(*Why axiom*) Lemma alloc_extern_def :
  forall (A1:Set),
  (forall (a:(alloc_table A1)),
   (forall (p:(pointer A1)),
    ((alloc_extern a p) ->
     (forall (q:(pointer A1)),
      ((offset_min a q) <= (offset_max a q) -> (full_separated p q)))))).
Admitted.

