(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)
Require Export Why.

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

(*Why type*) Definition block: Set ->Set.
Admitted.

(*Why logic*) Definition base_block :
  forall (A1:Set), (pointer A1) -> (block A1).
Admitted.
Implicit Arguments base_block.

(*Why logic*) Definition pointer_address :
  forall (A1:Set), (pointer A1) -> (pointer unit).
Admitted.
Implicit Arguments pointer_address.

(*Why logic*) Definition absolute_address : Z -> (pointer unit).
Admitted.

(*Why logic*) Definition address : forall (A1:Set), (pointer A1) -> Z.
Admitted.
Implicit Arguments address.

(*Why logic*) Definition offset_max :
  forall (A1:Set), (alloc_table A1) -> (pointer A1) -> Z.
Admitted.
Implicit Arguments offset_max.

(*Why logic*) Definition offset_min :
  forall (A1:Set), (alloc_table A1) -> (pointer A1) -> Z.
Admitted.
Implicit Arguments offset_min.

(*Why predicate*) Definition valid (A744:Set) (a:(alloc_table A744)) (p:(pointer A744))
  := (offset_min a p) <= 0 /\ (offset_max a p) >= 0.
Implicit Arguments valid.

(*Why predicate*) Definition same_block (A745:Set) (p:(pointer A745)) (q:(pointer A745))
  := (base_block p) = (base_block q).
Implicit Arguments same_block.

(*Why logic*) Definition shift :
  forall (A1:Set), (pointer A1) -> Z -> (pointer A1).
Admitted.
Implicit Arguments shift.

(*Why logic*) Definition null : forall (A1:Set), (pointer A1).
Admitted.
Set Contextual Implicit.
Implicit Arguments null.
Unset Contextual Implicit.

(*Why axiom*) Lemma address_injective :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)), (p = q <-> (address p) = (address q)))).
Admitted.

(*Why axiom*) Lemma address_null : forall (A1:Set), (address (@null A1)) = 0.
Admitted.

(*Why axiom*) Lemma address_positive :
  forall (A1:Set), (forall (p:(pointer A1)), 0 <= (address p)).
Admitted.

(*Why axiom*) Lemma address_shift_lt :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (i:Z),
    (forall (j:Z), ((address (shift p i)) < (address (shift p j)) <-> i < j)))).
Admitted.

(*Why axiom*) Lemma address_shift_le :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (i:Z),
    (forall (j:Z),
     ((address (shift p i)) <= (address (shift p j)) <-> i <= j)))).
Admitted.

(*Why axiom*) Lemma address_sub_pointer :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (i:Z),
    (forall (j:Z),
     ((address (shift p i)) <= (address (shift p j)) <-> i <= j)))).
Admitted.

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

(*Why axiom*) Lemma null_not_valid :
  forall (A1:Set), (forall (a:(alloc_table A1)), ~(valid a (@null A1))).
Admitted.

(*Why axiom*) Lemma null_pointer :
  forall (A1:Set),
  (forall (a:(alloc_table A1)), (offset_min a (@null A1)) >= 0 /\
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

(*Why predicate*) Definition pset_disjoint (A784:Set) (ps1:(pset A784)) (ps2:(pset A784))
  := (forall (p:(pointer A784)), ~((in_pset p ps1) /\ (in_pset p ps2))).
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

(*Why predicate*) Definition not_assigns (A801:Set) (A800:Set) (a:(alloc_table A800)) (m1:(memory A800 A801)) (m2:(memory A800 A801)) (l:(pset A800))
  := (forall (p:(pointer A800)),
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

(*Why predicate*) Definition instanceof (A820:Set) (a:(tag_table A820)) (p:(pointer A820)) (t:(tag_id A820))
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

(*Why predicate*) Definition root_tag (A825:Set) (t:(tag_id A825))
  := (parenttag t (@bottom_tag A825)).
Implicit Arguments root_tag.

(*Why axiom*) Lemma root_subtag :
  forall (A1:Set),
  (forall (a:(tag_id A1)),
   (forall (b:(tag_id A1)),
    (forall (c:(tag_id A1)),
     ((root_tag a) ->
      ((root_tag b) -> (~(a = b) -> ((subtag c a) -> ~(subtag c b)))))))).
Admitted.

(*Why predicate*) Definition fully_packed (A827:Set) (tag_table:(tag_table A827)) (mutable:(memory A827 (tag_id A827))) (this:(pointer A827))
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

(*Why predicate*) Definition alloc_fresh (A829:Set) (a:(alloc_table A829)) (p:(pointer A829)) (n:Z)
  := (forall (i:Z), (0 <= i /\ i < n -> ~(valid a (shift p i)))).
Implicit Arguments alloc_fresh.

(*Why axiom*) Lemma alloc_extends_offset_min :
  forall (A1:Set),
  (forall (a1:(alloc_table A1)),
   (forall (a2:(alloc_table A1)),
    ((alloc_extends a1 a2) ->
     (forall (p:(pointer A1)),
      ((valid a1 p) -> (offset_min a1 p) = (offset_min a2 p)))))).
Admitted.

(*Why axiom*) Lemma alloc_extends_offset_max :
  forall (A1:Set),
  (forall (a1:(alloc_table A1)),
   (forall (a2:(alloc_table A1)),
    ((alloc_extends a1 a2) ->
     (forall (p:(pointer A1)),
      ((valid a1 p) -> (offset_max a1 p) = (offset_max a2 p)))))).
Admitted.

(*Why logic*) Definition alloc_extends_except :
  forall (A1:Set), (alloc_table A1) -> (alloc_table A1) -> (pset A1) -> Prop.
Admitted.
Implicit Arguments alloc_extends_except.

(*Why axiom*) Lemma alloc_extends_except_offset_min :
  forall (A1:Set),
  (forall (a1:(alloc_table A1)),
   (forall (a2:(alloc_table A1)),
    (forall (l:(pset A1)),
     ((alloc_extends_except a1 a2 l) ->
      (forall (p:(pointer A1)),
       ((valid a1 p) /\ ~(in_pset p l) -> (offset_min a1 p) =
        (offset_min a2 p))))))).
Admitted.

(*Why axiom*) Lemma alloc_extends_except_offset_max :
  forall (A1:Set),
  (forall (a1:(alloc_table A1)),
   (forall (a2:(alloc_table A1)),
    (forall (l:(pset A1)),
     ((alloc_extends_except a1 a2 l) ->
      (forall (p:(pointer A1)),
       ((valid a1 p) /\ ~(in_pset p l) -> (offset_max a1 p) =
        (offset_max a2 p))))))).
Admitted.

(*Why type*) Definition bitvector: Set.
Admitted.

(*Why logic*) Definition concat_bitvector :
  bitvector -> bitvector -> bitvector.
Admitted.

(*Why logic*) Definition offset_min_bytes :
  forall (A1:Set), (alloc_table A1) -> (pointer A1) -> Z -> Z.
Admitted.
Implicit Arguments offset_min_bytes.

(*Why logic*) Definition offset_max_bytes :
  forall (A1:Set), (alloc_table A1) -> (pointer A1) -> Z -> Z.
Admitted.
Implicit Arguments offset_max_bytes.

(*Why axiom*) Lemma offset_min_bytes_def :
  forall (A1:Set),
  (forall (a:(alloc_table A1)),
   (forall (p:(pointer A1)),
    (forall (s:Z),
     (0 < s -> (offset_min a p) <= (s * (offset_min_bytes a p s)) /\
      (s * (offset_min_bytes a p s) - s) < (offset_min a p))))).
Admitted.

(*Why axiom*) Lemma offset_max_bytes_def :
  forall (A1:Set),
  (forall (a:(alloc_table A1)),
   (forall (p:(pointer A1)),
    (forall (s:Z),
     (0 < s -> (s * (offset_max_bytes a p s) + s - 1) <= (offset_max a p) /\
      (offset_max a p) < (s * (offset_max_bytes a p s) + s + s - 1))))).
Admitted.

(*Why logic*) Definition extract_bytes : bitvector -> Z -> Z -> bitvector.
Admitted.

(*Why logic*) Definition replace_bytes :
  bitvector -> Z -> Z -> bitvector -> bitvector.
Admitted.

(*Why axiom*) Lemma select_store_eq_union :
  (forall (o1:Z),
   (forall (s1:Z),
    (forall (o2:Z),
     (forall (s2:Z),
      (forall (v1:bitvector),
       (forall (v2:bitvector),
        (o1 = o2 /\ s1 = s2 ->
         (extract_bytes (replace_bytes v1 o1 s1 v2) o2 s2) = v2))))))).
Admitted.

(*Why axiom*) Lemma select_store_neq_union :
  (forall (o1:Z),
   (forall (s1:Z),
    (forall (o2:Z),
     (forall (s2:Z),
      (forall (v1:bitvector),
       (forall (v2:bitvector),
        ((o2 + s2) <= o1 \/ (o1 + s2) <= o2 ->
         (extract_bytes (replace_bytes v1 o1 s1 v2) o2 s2) =
         (extract_bytes v1 o2 s2)))))))).
Admitted.

(*Why axiom*) Lemma concat_replace_bytes_up :
  (forall (o1:Z),
   (forall (s1:Z),
    (forall (o2:Z),
     (forall (s2:Z),
      (forall (v1:bitvector),
       (forall (v2:bitvector),
        (forall (v3:bitvector),
         ((o1 + s1) = o2 ->
          (replace_bytes (replace_bytes v1 o1 s1 v2) o2 s2 v3) =
          (replace_bytes v1 o1 (s1 + s2) (concat_bitvector v2 v3)))))))))).
Admitted.

(*Why axiom*) Lemma concat_replace_bytes_down :
  (forall (o1:Z),
   (forall (s1:Z),
    (forall (o2:Z),
     (forall (s2:Z),
      (forall (v1:bitvector),
       (forall (v2:bitvector),
        (forall (v3:bitvector),
         ((o2 + s2) = o1 ->
          (replace_bytes (replace_bytes v1 o1 s1 v2) o2 s2 v3) =
          (replace_bytes v1 o2 (s1 + s2) (concat_bitvector v3 v2)))))))))).
Admitted.

(*Why axiom*) Lemma concat_extract_bytes :
  (forall (o1:Z),
   (forall (s1:Z),
    (forall (o2:Z),
     (forall (s2:Z),
      (forall (v:bitvector),
       ((o1 + s1) = o2 ->
        (concat_bitvector (extract_bytes v o1 s1) (extract_bytes v o2 s2)) =
        (extract_bytes v o1 (s1 + s2)))))))).
Admitted.

(*Why logic*) Definition select_bytes :
  forall (A1:Set), (memory A1 bitvector) -> (pointer A1) -> Z
  -> Z -> bitvector.
Admitted.
Implicit Arguments select_bytes.

(*Why logic*) Definition store_bytes :
  forall (A1:Set), (memory A1 bitvector) -> (pointer A1) -> Z -> Z
  -> bitvector -> (memory A1 bitvector).
Admitted.
Implicit Arguments store_bytes.

(*Why axiom*) Lemma select_store_eq_bytes :
  forall (A1:Set),
  (forall (m:(memory A1 bitvector)),
   (forall (p1:(pointer A1)),
    (forall (p2:(pointer A1)),
     (forall (o1:Z),
      (forall (s1:Z),
       (forall (o2:Z),
        (forall (s2:Z),
         (forall (v:bitvector),
          (p1 = p2 /\ o1 = o2 /\ s1 = s2 ->
           (select_bytes (store_bytes m p1 o1 s1 v) p2 o2 s2) = v))))))))).
Admitted.

(*Why axiom*) Lemma select_store_neq_bytes :
  forall (A1:Set),
  (forall (m:(memory A1 bitvector)),
   (forall (p1:(pointer A1)),
    (forall (p2:(pointer A1)),
     (forall (o1:Z),
      (forall (s1:Z),
       (forall (o2:Z),
        (forall (s2:Z),
         (forall (v:bitvector),
          ((pset_disjoint
            (pset_range (pset_singleton p1) o1 (o1 + s1)) (pset_range
                                                           (pset_singleton p2) o2 
                                                           (o2 + s2))) ->
           (select_bytes (store_bytes m p1 o1 s1 v) p2 o2 s2) =
           (select_bytes m p2 o2 s2)))))))))).
Admitted.

(*Why axiom*) Lemma shift_store_bytes :
  forall (A1:Set),
  (forall (m:(memory A1 bitvector)),
   (forall (p:(pointer A1)),
    (forall (i:Z),
     (forall (o:Z),
      (forall (s:Z),
       (forall (v:bitvector),
        (store_bytes m (shift p i) o s v) = (store_bytes m p (o + i) s v))))))).
Admitted.

(*Why axiom*) Lemma shift_select_bytes :
  forall (A1:Set),
  (forall (m:(memory A1 bitvector)),
   (forall (p:(pointer A1)),
    (forall (i:Z),
     (forall (o:Z),
      (forall (s:Z),
       (forall (v:bitvector),
        (select_bytes m (shift p i) o s) = (select_bytes m p (o + i) s))))))).
Admitted.

(*Why axiom*) Lemma concat_store_bytes_up :
  forall (A1:Set),
  (forall (m:(memory A1 bitvector)),
   (forall (p:(pointer A1)),
    (forall (o1:Z),
     (forall (s1:Z),
      (forall (o2:Z),
       (forall (s2:Z),
        (forall (v1:bitvector),
         (forall (v2:bitvector),
          ((o1 + s1) = o2 ->
           (store_bytes (store_bytes m p o1 s1 v1) p o2 s2 v2) =
           (store_bytes m p o1 (s1 + s2) (concat_bitvector v1 v2))))))))))).
Admitted.

(*Why axiom*) Lemma concat_store_bytes_down :
  forall (A1:Set),
  (forall (m:(memory A1 bitvector)),
   (forall (p:(pointer A1)),
    (forall (o1:Z),
     (forall (s1:Z),
      (forall (o2:Z),
       (forall (s2:Z),
        (forall (v1:bitvector),
         (forall (v2:bitvector),
          ((o2 + s2) = o1 ->
           (store_bytes (store_bytes m p o1 s1 v1) p o2 s2 v2) =
           (store_bytes m p o2 (s1 + s2) (concat_bitvector v2 v1))))))))))).
Admitted.

(*Why axiom*) Lemma concat_select_bytes :
  forall (A1:Set),
  (forall (m:(memory A1 bitvector)),
   (forall (p:(pointer A1)),
    (forall (o1:Z),
     (forall (s1:Z),
      (forall (o2:Z),
       (forall (s2:Z),
        ((o1 + s1) = o2 ->
         (concat_bitvector (select_bytes m p o1 s1) (select_bytes m p o2 s2)) =
         (select_bytes m p o1 (s1 + s2))))))))).
Admitted.

