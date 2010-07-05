(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)
Require Export Why.

(*Why logic*) Definition bool_and : bool -> bool -> bool.
Admitted.

(*Why logic*) Definition bool_or : bool -> bool -> bool.
Admitted.

(*Why logic*) Definition bool_xor : bool -> bool -> bool.
Admitted.

(*Why logic*) Definition bool_not : bool -> bool.
Admitted.

(*Why axiom*) Lemma bool_and_def :
  (forall (a:bool),
   (forall (b:bool), ((bool_and a b) = true <-> a = true /\ b = true))).
Admitted.

(*Why axiom*) Lemma bool_or_def :
  (forall (a:bool),
   (forall (b:bool), ((bool_or a b) = true <-> a = true \/ b = true))).
Admitted.

(*Why axiom*) Lemma bool_xor_def :
  (forall (a:bool), (forall (b:bool), ((bool_xor a b) = true <-> ~(a = b)))).
Admitted.

(*Why axiom*) Lemma bool_not_def :
  (forall (a:bool), ((bool_not a) = true <-> a = false)).
Admitted.

(*Why logic*) Definition ite : forall (A1:Set), bool -> A1 -> A1 -> A1.
Admitted.
Implicit Arguments ite.

(*Why axiom*) Lemma ite_true :
  forall (A1:Set),
  (forall (x:A1), (forall (y:A1), (if_then_else true x y) = x)).
Admitted.

(*Why axiom*) Lemma ite_false :
  forall (A1:Set),
  (forall (x:A1), (forall (y:A1), (if_then_else false x y) = y)).
Admitted.

(*Why logic*) Definition lt_int_bool : Z -> Z -> bool.
Admitted.

(*Why logic*) Definition le_int_bool : Z -> Z -> bool.
Admitted.

(*Why logic*) Definition gt_int_bool : Z -> Z -> bool.
Admitted.

(*Why logic*) Definition ge_int_bool : Z -> Z -> bool.
Admitted.

(*Why logic*) Definition eq_int_bool : Z -> Z -> bool.
Admitted.

(*Why logic*) Definition neq_int_bool : Z -> Z -> bool.
Admitted.

(*Why axiom*) Lemma lt_int_bool_axiom :
  (forall (x:Z), (forall (y:Z), ((lt_int_bool x y) = true <-> x < y))).
Admitted.

(*Why axiom*) Lemma le_int_bool_axiom :
  (forall (x:Z), (forall (y:Z), ((le_int_bool x y) = true <-> x <= y))).
Admitted.

(*Why axiom*) Lemma gt_int_bool_axiom :
  (forall (x:Z), (forall (y:Z), ((gt_int_bool x y) = true <-> x > y))).
Admitted.

(*Why axiom*) Lemma ge_int_bool_axiom :
  (forall (x:Z), (forall (y:Z), ((ge_int_bool x y) = true <-> x >= y))).
Admitted.

(*Why axiom*) Lemma eq_int_bool_axiom :
  (forall (x:Z), (forall (y:Z), ((eq_int_bool x y) = true <-> x = y))).
Admitted.

(*Why axiom*) Lemma neq_int_bool_axiom :
  (forall (x:Z), (forall (y:Z), ((neq_int_bool x y) = true <-> x <> y))).
Admitted.

(*Why logic*) Definition abs_int : Z -> Z.
Admitted.

(*Why axiom*) Lemma abs_int_pos :
  (forall (x:Z), (x >= 0 -> (abs_int x) = x)).
Admitted.

(*Why axiom*) Lemma abs_int_neg :
  (forall (x:Z), (x <= 0 -> (abs_int x) = (Zopp x))).
Admitted.

(*Why logic*) Definition int_max : Z -> Z -> Z.
Admitted.

(*Why logic*) Definition int_min : Z -> Z -> Z.
Admitted.

(*Why axiom*) Lemma int_max_is_ge :
  (forall (x:Z), (forall (y:Z), (int_max x y) >= x /\ (int_max x y) >= y)).
Admitted.

(*Why axiom*) Lemma int_max_is_some :
  (forall (x:Z), (forall (y:Z), (int_max x y) = x \/ (int_max x y) = y)).
Admitted.

(*Why axiom*) Lemma int_min_is_le :
  (forall (x:Z), (forall (y:Z), (int_min x y) <= x /\ (int_min x y) <= y)).
Admitted.

(*Why axiom*) Lemma int_min_is_some :
  (forall (x:Z), (forall (y:Z), (int_min x y) = x \/ (int_min x y) = y)).
Admitted.

Require Import Reals.

(*Why logic*) Definition lt_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition le_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition gt_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition ge_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition eq_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition neq_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition add_real : R -> R -> R.
Admitted.

(*Why logic*) Definition sub_real : R -> R -> R.
Admitted.

(*Why logic*) Definition mul_real : R -> R -> R.
Admitted.

(*Why logic*) Definition div_real : R -> R -> R.
Admitted.

(*Why logic*) Definition neg_real : R -> R.
Admitted.

(*Why logic*) Definition real_of_int : Z -> R.
Admitted.

(*Why axiom*) Lemma real_of_int_zero : (eq (IZR 0) (0)%R).
Admitted.

(*Why axiom*) Lemma real_of_int_one : (eq (IZR 1) (1)%R).
Admitted.

(*Why axiom*) Lemma real_of_int_add :
  (forall (x:Z), (forall (y:Z), (eq (IZR (x + y)) (Rplus (IZR x) (IZR y))))).
Admitted.

(*Why axiom*) Lemma real_of_int_sub :
  (forall (x:Z), (forall (y:Z), (eq (IZR (x - y)) (Rminus (IZR x) (IZR y))))).
Admitted.

(*Why logic*) Definition truncate_real_to_int : R -> Z.
Admitted.

(*Why axiom*) Lemma truncate_down_pos :
  (forall (x:R),
   ((Rge x (0)%R) -> (Rle (IZR (truncate_real_to_int x)) x) /\
    (Rlt x (IZR ((truncate_real_to_int x) + 1))))).
Admitted.

(*Why axiom*) Lemma truncate_up_neg :
  (forall (x:R),
   ((Rle x (0)%R) -> (Rlt (IZR ((truncate_real_to_int x) - 1)) x) /\
    (Rle x (IZR (truncate_real_to_int x))))).
Admitted.

(*Why logic*) Definition floor_real_to_int : R -> Z.
Admitted.

(*Why logic*) Definition ceil_real_to_int : R -> Z.
Admitted.

(*Why logic*) Definition lt_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition le_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition gt_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition ge_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition eq_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition neq_real_bool : R -> R -> bool.
Admitted.

(*Why axiom*) Lemma lt_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((lt_real_bool x y) = true <-> (Rlt x y)))).
Admitted.

(*Why axiom*) Lemma le_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((le_real_bool x y) = true <-> (Rle x y)))).
Admitted.

(*Why axiom*) Lemma gt_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((gt_real_bool x y) = true <-> (Rgt x y)))).
Admitted.

(*Why axiom*) Lemma ge_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((ge_real_bool x y) = true <-> (Rge x y)))).
Admitted.

(*Why axiom*) Lemma eq_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((eq_real_bool x y) = true <-> (eq x y)))).
Admitted.

(*Why axiom*) Lemma neq_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((neq_real_bool x y) = true <-> ~(eq x y)))).
Admitted.

(*Why logic*) Definition real_max : R -> R -> R.
Admitted.

(*Why logic*) Definition real_min : R -> R -> R.
Admitted.

(*Why axiom*) Lemma real_max_is_ge :
  (forall (x:R),
   (forall (y:R), (Rge (real_max x y) x) /\ (Rge (real_max x y) y))).
Admitted.

(*Why axiom*) Lemma real_max_is_some :
  (forall (x:R),
   (forall (y:R), (eq (real_max x y) x) \/ (eq (real_max x y) y))).
Admitted.

(*Why axiom*) Lemma real_min_is_le :
  (forall (x:R),
   (forall (y:R), (Rle (real_min x y) x) /\ (Rle (real_min x y) y))).
Admitted.

(*Why axiom*) Lemma real_min_is_some :
  (forall (x:R),
   (forall (y:R), (eq (real_min x y) x) \/ (eq (real_min x y) y))).
Admitted.

(*Why function*) Definition sqr_real  (x:R) := (Rmult x x).

(*Why logic*) Definition sqrt_real : R -> R.
Admitted.

(*Why axiom*) Lemma sqrt_pos :
  (forall (x:R), ((Rge x (0)%R) -> (Rge (sqrt x) (0)%R))).
Admitted.

(*Why axiom*) Lemma sqrt_sqr :
  (forall (x:R), ((Rge x (0)%R) -> (eq (sqr_real (sqrt x)) x))).
Admitted.

(*Why axiom*) Lemma sqr_sqrt :
  (forall (x:R), ((Rge x (0)%R) -> (eq (sqrt (Rmult x x)) x))).
Admitted.

(*Why logic*) Definition pow_real : R -> R -> R.
Admitted.

(*Why logic*) Definition abs_real : R -> R.
Admitted.

(*Why axiom*) Lemma abs_real_pos :
  (forall (x:R), ((Rge x (0)%R) -> (eq (Rabs x) x))).
Admitted.

(*Why axiom*) Lemma abs_real_neg :
  (forall (x:R), ((Rle x (0)%R) -> (eq (Rabs x) (Ropp x)))).
Admitted.

(*Why logic*) Definition exp : R -> R.
Admitted.

(*Why logic*) Definition log : R -> R.
Admitted.

(*Why logic*) Definition log10 : R -> R.
Admitted.

(*Why axiom*) Lemma log_exp : (forall (x:R), (eq (log (exp x)) x)).
Admitted.

(*Why axiom*) Lemma exp_log :
  (forall (x:R), ((Rgt x (0)%R) -> (eq (exp (log x)) x))).
Admitted.

(*Why logic*) Definition cos : R -> R.
Admitted.

(*Why logic*) Definition sin : R -> R.
Admitted.

(*Why logic*) Definition tan : R -> R.
Admitted.

(*Why logic*) Definition pi : R.
Admitted.

(*Why logic*) Definition cosh : R -> R.
Admitted.

(*Why logic*) Definition sinh : R -> R.
Admitted.

(*Why logic*) Definition tanh : R -> R.
Admitted.

(*Why logic*) Definition acos : R -> R.
Admitted.

(*Why logic*) Definition asin : R -> R.
Admitted.

(*Why logic*) Definition atan : R -> R.
Admitted.

(*Why logic*) Definition atan2 : R -> R -> R.
Admitted.

(*Why logic*) Definition hypot : R -> R -> R.
Admitted.

(*Why axiom*) Lemma prod_pos :
  (forall (x:R),
   (forall (y:R),
    (((Rgt x (0)%R) /\ (Rgt y (0)%R) -> (Rgt (Rmult x y) (0)%R))) /\
    (((Rlt x (0)%R) /\ (Rlt y (0)%R) -> (Rgt (Rmult x y) (0)%R))))).
Admitted.

(*Why axiom*) Lemma abs_minus :
  (forall (x:R), (eq (Rabs (Ropp x)) (Rabs x))).
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

(*Why logic*) Definition offset_max :
  forall (A1:Set), (alloc_table A1) -> (pointer A1) -> Z.
Admitted.
Implicit Arguments offset_max.

(*Why logic*) Definition offset_min :
  forall (A1:Set), (alloc_table A1) -> (pointer A1) -> Z.
Admitted.
Implicit Arguments offset_min.

(*Why predicate*) Definition valid (A707:Set) (a:(alloc_table A707)) (p:(pointer A707))
  := (offset_min a p) <= 0 /\ (offset_max a p) >= 0.
Implicit Arguments valid.

(*Why predicate*) Definition same_block (A708:Set) (p:(pointer A708)) (q:(pointer A708))
  := (base_block p) = (base_block q).
Implicit Arguments same_block.

(*Why logic*) Definition sub_pointer :
  forall (A1:Set), (pointer A1) -> (pointer A1) -> Z.
Admitted.
Implicit Arguments sub_pointer.

(*Why logic*) Definition shift :
  forall (A1:Set), (pointer A1) -> Z -> (pointer A1).
Admitted.
Implicit Arguments shift.

(*Why logic*) Definition null : forall (A1:Set), (pointer A1).
Admitted.
Set Contextual Implicit.
Implicit Arguments null.
Unset Contextual Implicit.

(*Why logic*) Definition pointer_address :
  forall (A1:Set), (pointer A1) -> (pointer unit).
Admitted.
Implicit Arguments pointer_address.

(*Why logic*) Definition absolute_address : Z -> (pointer unit).
Admitted.

(*Why logic*) Definition address : forall (A1:Set), (pointer A1) -> Z.
Admitted.
Implicit Arguments address.

Implicit Arguments offset_max.

Implicit Arguments offset_min.

Implicit Arguments valid.

Implicit Arguments same_block.

Implicit Arguments sub_pointer.

Implicit Arguments shift.

(*Why axiom*) Lemma address_injective :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)), (p = q <-> (address p) = (address q)))).
Admitted.

(*Why axiom*) Lemma address_null : forall (A1:Set), (address (@null A1)) = 0.
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
   (offset_max a (@null A1)) <= (-2)).
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

(*Why axiom*) Lemma same_block_shift_right :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)),
    (forall (i:Z), ((same_block p q) -> (same_block p (shift q i)))))).
Admitted.

(*Why axiom*) Lemma same_block_shift_left :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)),
    (forall (i:Z), ((same_block q p) -> (same_block (shift q i) p))))).
Admitted.

(*Why axiom*) Lemma sub_pointer_shift :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)),
    ((same_block p q) -> p = (shift q (sub_pointer p q))))).
Admitted.

(*Why axiom*) Lemma sub_pointer_self :
  forall (A1:Set), (forall (p:(pointer A1)), (sub_pointer p p) = 0).
Admitted.

(*Why axiom*) Lemma sub_pointer_zero :
  forall (A1:Set),
  (forall (p:(pointer A1)),
   (forall (q:(pointer A1)),
    ((same_block p q) -> ((sub_pointer p q) = 0 -> p = q)))).
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

(*Why predicate*) Definition pset_disjoint (A755:Set) (ps1:(pset A755)) (ps2:(pset A755))
  := (forall (p:(pointer A755)), ~((in_pset p ps1) /\ (in_pset p ps2))).
Implicit Arguments pset_disjoint.

(*Why predicate*) Definition pset_included (A756:Set) (ps1:(pset A756)) (ps2:(pset A756))
  := (forall (p:(pointer A756)), ((in_pset p ps1) -> (in_pset p ps2))).
Implicit Arguments pset_included.

(*Why axiom*) Lemma pset_included_self :
  forall (A1:Set), (forall (ps:(pset A1)), (pset_included ps ps)).
Admitted.

(*Why axiom*) Lemma pset_included_range :
  forall (A1:Set),
  (forall (ps:(pset A1)),
   (forall (a:Z),
    (forall (b:Z),
     (forall (c:Z),
      (forall (d:Z),
       (c <= a /\ b <= d ->
        (pset_included (pset_range ps a b) (pset_range ps c d)))))))).
Admitted.

(*Why axiom*) Lemma pset_included_range_all :
  forall (A1:Set),
  (forall (ps:(pset A1)),
   (forall (a:Z),
    (forall (b:Z),
     (forall (c:Z),
      (forall (d:Z), (pset_included (pset_range ps a b) (pset_all ps))))))).
Admitted.

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

(*Why predicate*) Definition not_assigns (A776:Set) (A775:Set) (a:(alloc_table A775)) (m1:(memory A775 A776)) (m2:(memory A775 A776)) (l:(pset A775))
  := (forall (p:(pointer A775)),
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

(*Why predicate*) Definition instanceof (A795:Set) (a:(tag_table A795)) (p:(pointer A795)) (t:(tag_id A795))
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

(*Why predicate*) Definition root_tag (A800:Set) (t:(tag_id A800))
  := (parenttag t (@bottom_tag A800)).
Implicit Arguments root_tag.

(*Why axiom*) Lemma root_subtag :
  forall (A1:Set),
  (forall (a:(tag_id A1)),
   (forall (b:(tag_id A1)),
    (forall (c:(tag_id A1)),
     ((root_tag a) ->
      ((root_tag b) -> (~(a = b) -> ((subtag c a) -> ~(subtag c b)))))))).
Admitted.

(*Why predicate*) Definition fully_packed (A802:Set) (tag_table:(tag_table A802)) (mutable:(memory A802 (tag_id A802))) (this:(pointer A802))
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

(*Why predicate*) Definition alloc_fresh (A804:Set) (a:(alloc_table A804)) (p:(pointer A804)) (n:Z)
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

(*Why axiom*) Lemma alloc_extends_not_assigns_empty :
  forall (A1:Set), forall (A2:Set),
  (forall (a1:(alloc_table A1)),
   (forall (a2:(alloc_table A1)),
    (forall (m1:(memory A1 A2)),
     (forall (m2:(memory A1 A2)),
      (forall (l:(pset A1)),
       (forall (p:(pointer A1)),
        (forall (n:Z),
         ((alloc_extends a1 a2) /\ (alloc_fresh a1 p n) /\
          (not_assigns a2 m1 m2 l) /\
          (pset_included l (pset_all (pset_singleton p))) ->
          (not_assigns a1 m1 m2 (@pset_empty A1)))))))))).
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

(*Why type*) Definition mybag: Set ->Set.
Admitted.

(*Why logic*) Definition in_mybag :
  forall (A1:Set), A1 -> (mybag A1) -> Prop.
Admitted.
Implicit Arguments in_mybag.

(*Why logic*) Definition disj_mybag :
  forall (A1:Set), (mybag A1) -> (mybag A1) -> Prop.
Admitted.
Implicit Arguments disj_mybag.

(*Why axiom*) Lemma disj_sym :
  forall (A1:Set),
  (forall (s1:(mybag A1)),
   (forall (s2:(mybag A1)), ((disj_mybag s1 s2) -> (disj_mybag s2 s1)))).
Admitted.

(*Why logic*) Definition frame_between :
  forall (A1:Set), forall (A2:Set), (mybag (pointer A1)) -> (memory A1 A2)
  -> (memory A1 A2) -> Prop.
Admitted.
Implicit Arguments frame_between.

(*Why axiom*) Lemma refl :
  forall (A1:Set), forall (A2:Set),
  (forall (sa:(mybag (pointer A1))),
   (forall (m:(memory A1 A2)), (frame_between sa m m))).
Admitted.

(*Why axiom*) Lemma gen :
  forall (A1:Set), forall (A2:Set),
  (forall (sa:(mybag (pointer A1))),
   (forall (m1:(memory A1 A2)),
    (forall (m2:(memory A1 A2)),
     (forall (p:(pointer A1)),
      (forall (v:A2),
       ((frame_between sa m1 m2) ->
        (~(in_mybag p sa) -> (frame_between sa (store m1 p v) m2)))))))).
Admitted.

