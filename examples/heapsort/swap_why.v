(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Omega.

Lemma swap_po_1 : 
  (i: Z)
  (j: Z)
  (t: (array Z))
  (Pre5: (`0 <= i` /\ `i < (array_length t)`) /\ `0 <= j` /\
         `j < (array_length t)`)
  (Pre4: `0 <= i` /\ `i < (array_length t)`)
  (v: Z)
  (Post3: v = (access t i))
  (Pre2: `0 <= i` /\ `i < (array_length t)`)
  `0 <= j` /\ `j < (array_length t)`.
Proof.
Intros; Omega.
Save.

Lemma swap_po_2 : 
  (i: Z)
  (j: Z)
  (t: (array Z))
  (Pre5: (`0 <= i` /\ `i < (array_length t)`) /\ `0 <= j` /\
         `j < (array_length t)`)
  (Pre4: `0 <= i` /\ `i < (array_length t)`)
  (v: Z)
  (Post3: v = (access t i))
  (Pre2: `0 <= i` /\ `i < (array_length t)`)
  (Pre3: `0 <= j` /\ `j < (array_length t)`)
  (t0: (array Z))
  (Post1: t0 = (store t i (access t j)))
  `0 <= j` /\ `j < (array_length t0)`.
Proof.
Intros; ArraySubst t0.
Save.

Lemma swap_po_3 : 
  (i: Z)
  (j: Z)
  (t: (array Z))
  (Pre5: (`0 <= i` /\ `i < (array_length t)`) /\ `0 <= j` /\
         `j < (array_length t)`)
  (Pre4: `0 <= i` /\ `i < (array_length t)`)
  (v: Z)
  (Post3: v = (access t i))
  (Pre2: `0 <= i` /\ `i < (array_length t)`)
  (Pre3: `0 <= j` /\ `j < (array_length t)`)
  (t0: (array Z))
  (Post1: t0 = (store t i (access t j)))
  (Pre1: `0 <= j` /\ `j < (array_length t0)`)
  (t1: (array Z))
  (Post2: t1 = (store t0 j v))
  (exchange t1 t i j).
Proof.
Intros; Subst t1 t0 v.
Auto with datatypes.
Save.

Definition swap := (* validation *)
  [i: Z; j: Z; t: (array Z); Pre5: (`0 <= i` /\ `i < (array_length t)`) /\
   `0 <= j` /\ `j < (array_length t)`]
    let Pre4 = (proj1 ? ? Pre5) in
    let (v, Post3) = (exist_1 [result: Z]result = (access t i) (access t i)
      (refl_equal ? (access t i))) in
    let (t0, result, Post4) =
      let Pre2 = Pre4 in
      let Pre3 = (swap_po_1 i j t Pre5 Pre4 v Post3 Pre2) in
      let (t0, result, Post1) = (exist_2 [t1: (array Z)][result1: unit]
        t1 = (store t i (access t j)) (store t i (access t j)) tt
        (refl_equal ? (store t i (access t j)))) in
      let Pre1 = (swap_po_2 i j t Pre5 Pre4 v Post3 Pre2 Pre3 t0 Post1) in
      let (t1, result0, Post2) = (exist_2 [t2: (array Z)][result2: unit]
        t2 = (store t0 j v) (store t0 j v) tt
        (refl_equal ? (store t0 j v))) in
      (exist_2 [t2: (array Z)][result1: unit](exchange t2 t i j) t1 result0
      (swap_po_3 i j t Pre5 Pre4 v Post3 Pre2 Pre3 t0 Post1 Pre1 t1 Post2)) in
    (exist_2 [t1: (array Z)][result0: unit](exchange t1 t i j) t0 result
    Post4).

