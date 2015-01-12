(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export jessie_why.

(*Why type*) Definition Family: Set.
Admitted.

(*Why type*) Definition Person: Set.
Admitted.

(*Why logic*) Definition Family_inv :
  (pointer Family) -> (memory Person Z) -> (memory Person (pointer Family))
  -> (memory Family (pointer Person)) -> (memory Family
  (pointer Person)) -> Prop.
Admitted.

(*Why logic*) Definition Person_inv :
  (pointer Person) -> (memory Person Z) -> (memory Person (pointer Family))
  -> (memory Family (pointer Person)) -> (memory Family
  (pointer Person)) -> Prop.
Admitted.

(*Why axiom*) Lemma Family_inv_sem :
  (forall (mother:(memory Family (pointer Person))),
   (forall (father:(memory Family (pointer Person))),
    (forall (family:(memory Person (pointer Family))),
     (forall (age:(memory Person Z)),
      (forall (inv_this:(pointer Family)),
       ((Family_inv inv_this age family father mother) <->
        (~(inv_this = (@null Family)) ->
         (Person_inv (select mother inv_this) age family father mother) /\
         (Person_inv (select father inv_this) age family father mother)))))))).
Admitted.

(*Why logic*) Definition Family_tag : (tag_id Family).
Admitted.

(*Why predicate*) Definition age_inv  (age:(memory Person Z))
  (family:(memory Person (pointer Family))) (father:(memory Family
  (pointer Person))) (mother:(memory Family (pointer Person)))
  (age:(memory Person Z)) (this:(pointer Person))
  := (select age (select mother (select family this))) > (select age this) /\
     (select age (select father (select family this))) > (select age this).

Inductive valid_inv: forall C: Set, pointer C ->
  memory Family (pointer Person) -> (* mother *)
  memory Family (pointer Person) -> (* father *)
  memory Person (pointer Family) -> (* family *)
  memory Family Z -> (* age *)
  Prop :=
| vi_family_null:
    forall mother: memory Family (pointer Person),
    forall father: memory Family (pointer Person),
    forall family: memory Person (pointer Family),
    forall age: memory Person Z,
    forall x: pointer Family,
    x = @null Family ->
    valid_inv Family x mother father family age
| vi_person_null:
    forall mother: memory Family (pointer Person),
    forall father: memory Family (pointer Person),
    forall family: memory Person (pointer Family),
    forall age: memory Person Z,
    forall x: pointer Person,
    x = @null Person ->
    valid_inv Person x mother father family age
| vi_family:
    forall mother: memory Family (pointer Person),
    forall father: memory Family (pointer Person),
    forall family: memory Person (pointer Family),
    forall age: memory Person Z,
    forall x: pointer Family,
    x <> @null Family ->
    valid_inv Person (select mother x) mother father family age ->
    valid_inv Person (select father x) mother father family age ->
    valid_inv Family x mother father family age
| vi_person:
    forall mother: memory Family (pointer Person),
    forall father: memory Family (pointer Person),
    forall family: memory Person (pointer Family),
    forall age: memory Person Z,
    forall x: pointer Person,
    x <> @null Person ->
    valid_inv Family (select family x) mother father family age ->
    age_inv age family father mother age x ->
    valid_inv Person x mother father family age.
Hint Constructors valid_inv.

(*exact (fun x age family father mother =>
  valid_inv Family x mother father family age).
Defined.

exact (fun x age family father mother =>
  valid_inv Person x mother father family age).
Defined.

Proof.
unfold Person_inv; unfold Family_inv.
intros; split; intros; try split.
inversion H; subst; auto.
assert False as F; auto.
destruct F.
admit. (* Person = Family: absurde *)
admit. (* Person = Family: absurde *)
inversion H; subst; auto.
assert False as F; auto.
destruct F.
admit. (* Person = Family: absurde *)
admit. (* Person = Family: absurde *)
assert (inv_this = null Family \/ inv_this <> null Family).
admit. (* eq_pointer *)
destruct H0; subst.
apply vi_family_null; auto.
apply vi_family; auto.
apply (proj1 (H H0)).
apply (proj2 (H H0)).
Qed.

Admitted.*)

(*Why axiom*) Lemma Person_inv_sem :
  (forall (mother:(memory Family (pointer Person))),
   (forall (father:(memory Family (pointer Person))),
    (forall (family:(memory Person (pointer Family))),
     (forall (age:(memory Person Z)),
      (forall (inv_this:(pointer Person)),
       ((Person_inv inv_this age family father mother) <->
        (~(inv_this = (@null Person)) ->
         (Family_inv (select family inv_this) age family father mother) /\
         (age_inv age family father mother age inv_this)))))))).
Admitted.

(*Proof.
unfold Person_inv; unfold Family_inv.
intros; split; intros; try split.
inversion H; subst; auto.
admit. (* Person = Family: absurde *)
assert False as F; auto.
destruct F.
admit. (* Person = Family: absurde *)
inversion H; subst; auto.
admit. (* Person = Family: absurde *)
assert False as F; auto.
destruct F.
admit. (* Person = Family: absurde *)
assert (inv_this = null Person \/ inv_this <> null Person).
admit. (* eq_pointer *)
destruct H0; subst.
apply vi_person_null; auto.
apply vi_person; auto.
apply (proj1 (H H0)).
apply (proj2 (H H0)).
Qed.*)

(*Why logic*) Definition Person_tag : (tag_id Person).
Admitted.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma m_ensures_ok_po_1 : 
  forall (this: (pointer Person)),
  forall (Person_alloc_table: (alloc_table Person)),
  forall (Person_tag_table: (tag_table Person)),
  forall (age: (memory Person Z)),
  forall (family: (memory Person (pointer Family))),
  forall (father: (memory Family (pointer Person))),
  forall (mother: (memory Family (pointer Person))),
  forall (HW_1: ((((offset_min Person_alloc_table this) <= 0 /\
                (offset_max Person_alloc_table this) >= 0) /\
                (instanceof Person_tag_table this Person_tag)) /\
                (select age this) > 0) /\
                (Person_inv this age family father mother)),
  (valid Person_alloc_table this).
Proof.
intuition.
admit.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma m_ensures_ok_po_2 : 
  forall (this: (pointer Person)),
  forall (Person_alloc_table: (alloc_table Person)),
  forall (Person_tag_table: (tag_table Person)),
  forall (age: (memory Person Z)),
  forall (family: (memory Person (pointer Family))),
  forall (father: (memory Family (pointer Person))),
  forall (mother: (memory Family (pointer Person))),
  forall (HW_1: ((((offset_min Person_alloc_table this) <= 0 /\
                (offset_max Person_alloc_table this) >= 0) /\
                (instanceof Person_tag_table this Person_tag)) /\
                (select age this) > 0) /\
                (Person_inv this age family father mother)),
  forall (HW_2: (valid Person_alloc_table this)),
  forall (age0: (memory Person Z)),
  forall (HW_3: age0 = (store age this 0)),
  (Person_inv this age0 family father mother).
Proof.
intros; subst.
destruct HW_1 as [H1 H2].
generalize (Person_inv_sem mother father family age this).
intro L.
destruct L as [L L2]; clear L2.
generalize (L H2).
intro H3.
apply (proj2 (Person_inv_sem mother father family (store age this 0) this)).
intro NN.
generalize (H3 NN).
intro H4.
destruct H4 as [H4 H5].
split.
admit.
unfold age_inv.
unfold age_inv in H5.

Check Family_inv_sem.
apply (proj2 (Family_inv_sem mother father family (store age this 0)
  (select family this))).
intro NN2.
split.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma older_ensures_ok_po_1 : 
  forall (p1: (pointer Person)),
  forall (p2: (pointer Person)),
  forall (Person_alloc_table: (alloc_table Person)),
  forall (Person_tag_table: (tag_table Person)),
  forall (age: (memory Person Z)),
  forall (family: (memory Person (pointer Family))),
  forall (father: (memory Family (pointer Person))),
  forall (mother: (memory Family (pointer Person))),
  forall (HW_1: ((((offset_min Person_alloc_table p1) <= 0 /\
                (offset_max Person_alloc_table p1) >= 0) /\
                (instanceof Person_tag_table p1 Person_tag)) /\
                ((offset_min Person_alloc_table p2) <= 0 /\
                (offset_max Person_alloc_table p2) >= 0) /\
                (instanceof Person_tag_table p2 Person_tag)) /\
                (Person_inv p1 age family father mother) /\
                (Person_inv p2 age family father mother)),
  (valid Person_alloc_table p1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma older_ensures_ok_po_2 : 
  forall (p1: (pointer Person)),
  forall (p2: (pointer Person)),
  forall (Person_alloc_table: (alloc_table Person)),
  forall (Person_tag_table: (tag_table Person)),
  forall (age: (memory Person Z)),
  forall (family: (memory Person (pointer Family))),
  forall (father: (memory Family (pointer Person))),
  forall (mother: (memory Family (pointer Person))),
  forall (HW_1: ((((offset_min Person_alloc_table p1) <= 0 /\
                (offset_max Person_alloc_table p1) >= 0) /\
                (instanceof Person_tag_table p1 Person_tag)) /\
                ((offset_min Person_alloc_table p2) <= 0 /\
                (offset_max Person_alloc_table p2) >= 0) /\
                (instanceof Person_tag_table p2 Person_tag)) /\
                (Person_inv p1 age family father mother) /\
                (Person_inv p2 age family father mother)),
  forall (HW_2: (valid Person_alloc_table p1)),
  forall (result: Z),
  forall (HW_3: result = (select age p1)),
  (valid Person_alloc_table p2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma older_ensures_ok_po_3 : 
  forall (p1: (pointer Person)),
  forall (p2: (pointer Person)),
  forall (Person_alloc_table: (alloc_table Person)),
  forall (Person_tag_table: (tag_table Person)),
  forall (age: (memory Person Z)),
  forall (family: (memory Person (pointer Family))),
  forall (father: (memory Family (pointer Person))),
  forall (mother: (memory Family (pointer Person))),
  forall (HW_1: ((((offset_min Person_alloc_table p1) <= 0 /\
                (offset_max Person_alloc_table p1) >= 0) /\
                (instanceof Person_tag_table p1 Person_tag)) /\
                ((offset_min Person_alloc_table p2) <= 0 /\
                (offset_max Person_alloc_table p2) >= 0) /\
                (instanceof Person_tag_table p2 Person_tag)) /\
                (Person_inv p1 age family father mother) /\
                (Person_inv p2 age family father mother)),
  forall (HW_2: (valid Person_alloc_table p1)),
  forall (result: Z),
  forall (HW_3: result = (select age p1)),
  forall (HW_4: (valid Person_alloc_table p2)),
  forall (result0: Z),
  forall (HW_5: result0 = (select age p2)),
  forall (HW_6: result > result0),
  forall (HW_7: true = true),
  (select age p1) > (select age p2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma older_ensures_ok_po_4 : 
  forall (p1: (pointer Person)),
  forall (p2: (pointer Person)),
  forall (Person_alloc_table: (alloc_table Person)),
  forall (Person_tag_table: (tag_table Person)),
  forall (age: (memory Person Z)),
  forall (family: (memory Person (pointer Family))),
  forall (father: (memory Family (pointer Person))),
  forall (mother: (memory Family (pointer Person))),
  forall (HW_1: ((((offset_min Person_alloc_table p1) <= 0 /\
                (offset_max Person_alloc_table p1) >= 0) /\
                (instanceof Person_tag_table p1 Person_tag)) /\
                ((offset_min Person_alloc_table p2) <= 0 /\
                (offset_max Person_alloc_table p2) >= 0) /\
                (instanceof Person_tag_table p2 Person_tag)) /\
                (Person_inv p1 age family father mother) /\
                (Person_inv p2 age family father mother)),
  forall (HW_2: (valid Person_alloc_table p1)),
  forall (result: Z),
  forall (HW_3: result = (select age p1)),
  forall (HW_4: (valid Person_alloc_table p2)),
  forall (result0: Z),
  forall (HW_5: result0 = (select age p2)),
  forall (HW_6: result > result0),
  (Person_inv p1 age family father mother).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma older_ensures_ok_po_5 : 
  forall (p1: (pointer Person)),
  forall (p2: (pointer Person)),
  forall (Person_alloc_table: (alloc_table Person)),
  forall (Person_tag_table: (tag_table Person)),
  forall (age: (memory Person Z)),
  forall (family: (memory Person (pointer Family))),
  forall (father: (memory Family (pointer Person))),
  forall (mother: (memory Family (pointer Person))),
  forall (HW_1: ((((offset_min Person_alloc_table p1) <= 0 /\
                (offset_max Person_alloc_table p1) >= 0) /\
                (instanceof Person_tag_table p1 Person_tag)) /\
                ((offset_min Person_alloc_table p2) <= 0 /\
                (offset_max Person_alloc_table p2) >= 0) /\
                (instanceof Person_tag_table p2 Person_tag)) /\
                (Person_inv p1 age family father mother) /\
                (Person_inv p2 age family father mother)),
  forall (HW_2: (valid Person_alloc_table p1)),
  forall (result: Z),
  forall (HW_3: result = (select age p1)),
  forall (HW_4: (valid Person_alloc_table p2)),
  forall (result0: Z),
  forall (HW_5: result0 = (select age p2)),
  forall (HW_6: result > result0),
  (Person_inv p2 age family father mother).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma older_ensures_ok_po_6 : 
  forall (p1: (pointer Person)),
  forall (p2: (pointer Person)),
  forall (Person_alloc_table: (alloc_table Person)),
  forall (Person_tag_table: (tag_table Person)),
  forall (age: (memory Person Z)),
  forall (family: (memory Person (pointer Family))),
  forall (father: (memory Family (pointer Person))),
  forall (mother: (memory Family (pointer Person))),
  forall (HW_1: ((((offset_min Person_alloc_table p1) <= 0 /\
                (offset_max Person_alloc_table p1) >= 0) /\
                (instanceof Person_tag_table p1 Person_tag)) /\
                ((offset_min Person_alloc_table p2) <= 0 /\
                (offset_max Person_alloc_table p2) >= 0) /\
                (instanceof Person_tag_table p2 Person_tag)) /\
                (Person_inv p1 age family father mother) /\
                (Person_inv p2 age family father mother)),
  forall (HW_2: (valid Person_alloc_table p1)),
  forall (result: Z),
  forall (HW_3: result = (select age p1)),
  forall (HW_4: (valid Person_alloc_table p2)),
  forall (result0: Z),
  forall (HW_5: result0 = (select age p2)),
  forall (HW_9: result <= result0),
  forall (HW_10: false = true),
  (select age p1) > (select age p2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma older_ensures_ok_po_7 : 
  forall (p1: (pointer Person)),
  forall (p2: (pointer Person)),
  forall (Person_alloc_table: (alloc_table Person)),
  forall (Person_tag_table: (tag_table Person)),
  forall (age: (memory Person Z)),
  forall (family: (memory Person (pointer Family))),
  forall (father: (memory Family (pointer Person))),
  forall (mother: (memory Family (pointer Person))),
  forall (HW_1: ((((offset_min Person_alloc_table p1) <= 0 /\
                (offset_max Person_alloc_table p1) >= 0) /\
                (instanceof Person_tag_table p1 Person_tag)) /\
                ((offset_min Person_alloc_table p2) <= 0 /\
                (offset_max Person_alloc_table p2) >= 0) /\
                (instanceof Person_tag_table p2 Person_tag)) /\
                (Person_inv p1 age family father mother) /\
                (Person_inv p2 age family father mother)),
  forall (HW_2: (valid Person_alloc_table p1)),
  forall (result: Z),
  forall (HW_3: result = (select age p1)),
  forall (HW_4: (valid Person_alloc_table p2)),
  forall (result0: Z),
  forall (HW_5: result0 = (select age p2)),
  forall (HW_9: result <= result0),
  forall (HW_11: (select age p1) > (select age p2)),
  false = true.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma older_ensures_ok_po_8 : 
  forall (p1: (pointer Person)),
  forall (p2: (pointer Person)),
  forall (Person_alloc_table: (alloc_table Person)),
  forall (Person_tag_table: (tag_table Person)),
  forall (age: (memory Person Z)),
  forall (family: (memory Person (pointer Family))),
  forall (father: (memory Family (pointer Person))),
  forall (mother: (memory Family (pointer Person))),
  forall (HW_1: ((((offset_min Person_alloc_table p1) <= 0 /\
                (offset_max Person_alloc_table p1) >= 0) /\
                (instanceof Person_tag_table p1 Person_tag)) /\
                ((offset_min Person_alloc_table p2) <= 0 /\
                (offset_max Person_alloc_table p2) >= 0) /\
                (instanceof Person_tag_table p2 Person_tag)) /\
                (Person_inv p1 age family father mother) /\
                (Person_inv p2 age family father mother)),
  forall (HW_2: (valid Person_alloc_table p1)),
  forall (result: Z),
  forall (HW_3: result = (select age p1)),
  forall (HW_4: (valid Person_alloc_table p2)),
  forall (result0: Z),
  forall (HW_5: result0 = (select age p2)),
  forall (HW_9: result <= result0),
  (Person_inv p1 age family father mother).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma older_ensures_ok_po_9 : 
  forall (p1: (pointer Person)),
  forall (p2: (pointer Person)),
  forall (Person_alloc_table: (alloc_table Person)),
  forall (Person_tag_table: (tag_table Person)),
  forall (age: (memory Person Z)),
  forall (family: (memory Person (pointer Family))),
  forall (father: (memory Family (pointer Person))),
  forall (mother: (memory Family (pointer Person))),
  forall (HW_1: ((((offset_min Person_alloc_table p1) <= 0 /\
                (offset_max Person_alloc_table p1) >= 0) /\
                (instanceof Person_tag_table p1 Person_tag)) /\
                ((offset_min Person_alloc_table p2) <= 0 /\
                (offset_max Person_alloc_table p2) >= 0) /\
                (instanceof Person_tag_table p2 Person_tag)) /\
                (Person_inv p1 age family father mother) /\
                (Person_inv p2 age family father mother)),
  forall (HW_2: (valid Person_alloc_table p1)),
  forall (result: Z),
  forall (HW_3: result = (select age p1)),
  forall (HW_4: (valid Person_alloc_table p2)),
  forall (result0: Z),
  forall (HW_5: result0 = (select age p2)),
  forall (HW_9: result <= result0),
  (Person_inv p2 age family father mother).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.
