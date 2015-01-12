(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

Inductive In [t:(array Z); l,u,v:Z] : Prop :=
  In_cons : (i:Z) `l <= i <= u` -> #t[i]=v -> (In t l u v).

Axiom le_mean : (x,y:Z)
  `0 <= x <= y` -> `x <= (x + y)/2`.

Axiom ge_mean : (x,y:Z)
  `0 <= x <= y` -> `(x + y)/2 <= y`.

Axiom In_right_side : (t:(array Z))(v:Z)
  (sorted_array t `0` `(array_length t)-1`) ->
  (l,u:Z)
  `0 <= l` -> `u <= (array_length t)-1` -> `l <= u` -> `l <= (l+u)/2 <= u` ->
  ((In t `0` `(array_length t)-1` v) -> (In t l u v)) ->
  `(access t ((l+u)/2)) < v` ->
  ((In t `0` `(array_length t)-1` v) -> (In t `(l+u)/2 + 1` u v)).

Axiom In_left_side : (t:(array Z))(v:Z)
  (sorted_array t `0` `(array_length t)-1`) ->
  (l,u:Z)
  `0 <= l` -> `u <= (array_length t)-1` -> `l <= u` -> `l <= (l+u)/2 <= u` ->
  ((In t `0` `(array_length t)-1` v) -> (In t l u v)) ->
  `(access t ((l+u)/2)) > v` ->
  ((In t `0` `(array_length t)-1` v) -> (In t l `(l+u)/2 - 1` v)).

(* Why obligation from file "bsearch.c", characters 631-642 *)
Lemma binary_search_po_1 : 
  (n: Z)
  (v: Z)
  (t: (array Z))
  (Pre8: `(array_length t) = n` /\ `n >= 0` /\ (sorted_array t `0` `n - 1`))
  (l1: Z)
  (Post1: l1 = `0`)
  (u1: Z)
  (Post2: u1 = `n - 1`)
  (Variant1: Z)
  (l2: Z)
  (u2: Z)
  (Pre7: Variant1 = `2 + u2 - l2`)
  (Pre6: `0 <= l2` /\ `u2 <= (array_length t) - 1` /\
         (((In t `0` `(array_length t) - 1` v) -> (In t l2 u2 v))))
  (Test2: `l2 <= u2`)
  ~(`2` = `0`).
Proof.
Intros; Omega.
Save.

(* Why obligation from file "bsearch.c", characters 660-677 *)
Lemma binary_search_po_2 : 
  (n: Z)
  (v: Z)
  (t: (array Z))
  (Pre8: `(array_length t) = n` /\ `n >= 0` /\ (sorted_array t `0` `n - 1`))
  (l1: Z)
  (Post1: l1 = `0`)
  (u1: Z)
  (Post2: u1 = `n - 1`)
  (Variant1: Z)
  (l2: Z)
  (u2: Z)
  (Pre7: Variant1 = `2 + u2 - l2`)
  (Pre6: `0 <= l2` /\ `u2 <= (array_length t) - 1` /\
         (((In t `0` `(array_length t) - 1` v) -> (In t l2 u2 v))))
  (Test2: `l2 <= u2`)
  (Pre5: ~(`2` = `0`))
  (m2: Z)
  (Post3: m2 = (Zdiv (`l2 + u2`) `2`))
  `l2 <= m2` /\ `m2 <= u2`.
Proof.
Intuition; Subst.
Apply le_mean; Omega.
Apply ge_mean; Omega.
Save.

(* Why obligation from file "bsearch.c", characters 677-680 *)
Lemma binary_search_po_3 : 
  (n: Z)
  (v: Z)
  (t: (array Z))
  (Pre8: `(array_length t) = n` /\ `n >= 0` /\ (sorted_array t `0` `n - 1`))
  (l1: Z)
  (Post1: l1 = `0`)
  (u1: Z)
  (Post2: u1 = `n - 1`)
  (Variant1: Z)
  (l2: Z)
  (u2: Z)
  (Pre7: Variant1 = `2 + u2 - l2`)
  (Pre6: `0 <= l2` /\ `u2 <= (array_length t) - 1` /\
         (((In t `0` `(array_length t) - 1` v) -> (In t l2 u2 v))))
  (Test2: `l2 <= u2`)
  (Pre5: ~(`2` = `0`))
  (m2: Z)
  (Post3: m2 = (Zdiv (`l2 + u2`) `2`))
  (Pre4: `l2 <= m2` /\ `m2 <= u2`)
  ((result:Z)
   (result = (access t m2) ->
    ((`result < v` ->
      ((l:Z)
       (l = `m2 + 1` -> (`0 <= l` /\ `u2 <= (array_length t) - 1` /\
        (((In t `0` `(array_length t) - 1` v) -> (In t l u2 v)))) /\
        (Zwf `0` `2 + u2 - l` `2 + u2 - l2`))))) /\
    ((`result >= v` ->
      ((result:Z)
       (result = (access t m2) ->
        ((`result > v` ->
          ((u:Z)
           (u = `m2 - 1` -> (`0 <= l2` /\ `u <= (array_length t) - 1` /\
            (((In t `0` `(array_length t) - 1` v) -> (In t l2 u v)))) /\
            (Zwf `0` `2 + u - l2` `2 + u2 - l2`))))) /\
        ((`result <= v` -> (`0 <= m2` /\ `m2 <= (array_length t) - 1`) /\
          `(access t m2) = v` \/ `m2 = (-1)` /\
          ~(In t `0` `(array_length t) - 1` v))))) /\
      `0 <= m2` /\ `m2 < (array_length t)`)))) /\
  `0 <= m2` /\ `m2 < (array_length t)`.
Proof.
Unfold Zwf; Intuition Try Omega.
Subst; Apply In_right_side; Intuition.
Rewrite H; Assumption.
Subst; Apply In_left_side; Intuition.
Rewrite H; Assumption.
Save.

(* Why obligation from file "bsearch.c", characters 504-596 *)
Lemma binary_search_po_4 : 
  (n: Z)
  (v: Z)
  (t: (array Z))
  (Pre8: `(array_length t) = n` /\ `n >= 0` /\ (sorted_array t `0` `n - 1`))
  (l1: Z)
  (Post1: l1 = `0`)
  (u1: Z)
  (Post2: u1 = `n - 1`)
  `0 <= l1` /\ `u1 <= (array_length t) - 1` /\
  (((In t `0` `(array_length t) - 1` v) -> (In t l1 u1 v))).
Proof.
Intuition.
Subst; Rewrite <- H; Assumption.
Save.

(* Why obligation from file "bsearch.c", characters 794-796 *)
Lemma binary_search_po_5 : 
  (n: Z)
  (v: Z)
  (t: (array Z))
  (Pre8: `(array_length t) = n` /\ `n >= 0` /\ (sorted_array t `0` `n - 1`))
  (l1: Z)
  (Post1: l1 = `0`)
  (u1: Z)
  (Post2: u1 = `n - 1`)
  (l2: Z)
  (u2: Z)
  (Post8: (`0 <= l2` /\ `u2 <= (array_length t) - 1` /\
          (((In t `0` `(array_length t) - 1` v) -> (In t l2 u2 v)))) /\
          `l2 > u2`)
  (`0 <= (-1)` /\ `(-1) <= (array_length t) - 1`) /\ `(access t (-1)) = v` \/
  `(-1) = (-1)` /\ ~(In t `0` `(array_length t) - 1` v).
Proof.
Intuition.
Right.
Split. Trivial.
Intuition.
Decompose [In] H7.
Absurd `l2 <= i <= u2`; Omega.
Save.
