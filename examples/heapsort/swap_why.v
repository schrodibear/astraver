(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Omega.

Lemma swap_po_1 : 
  (N: Z)
  (i: Z)
  (j: Z)
  (t: (array N Z))
  (Pre5: (`0 <= i` /\ `i < N`) /\ `0 <= j` /\ `j < N`)
  (Pre1: `0 <= i` /\ `i < N`)
  (v: Z)
  (Post3: v = (access t i))
  `0 <= j` /\ `j < N`.
Proof.
Intros; Omega.
Save.

Lemma swap_po_2 : 
  (N: Z)
  (i: Z)
  (j: Z)
  (t: (array N Z))
  (Pre5: (`0 <= i` /\ `i < N`) /\ `0 <= j` /\ `j < N`)
  (Pre1: `0 <= i` /\ `i < N`)
  (v: Z)
  (Post3: v = (access t i))
  (Pre2: `0 <= j` /\ `j < N`)
  (t0: (array N Z))
  (Post1: t0 = (store t i (access t j)))
  (t1: (array N Z))
  (Post2: t1 = (store t0 j v))
  (exchange t1 t i j).
Proof.
Intros; Subst t1 t0 v.
Auto with datatypes.
Save.

Definition swap := (* validation *)
  [N: Z; i: Z; j: Z; t: (array N Z); Pre5: (`0 <= i` /\ `i < N`) /\
   `0 <= j` /\ `j < N`]
    let Pre1 = (proj1 ? ? Pre5) in
    let (v, Post3) = (exist_1 [result: Z]result = (access t i) (access t i)
      (refl_equal ? (access t i))) in
    let (t0, result, Post4) =
      let Pre2 = (swap_po_1 N i j t Pre5 Pre1 v Post3) in
      let (t0, result, Post1) =
        let (result, Post1) = (exist_1 [result: Z]
          (store t i result) = (store t i (access t j)) (access t j)
          (refl_equal ? (store t i (access t j)))) in
        let Pre3 = Pre1 in
        (exist_2 [t1: (array N Z)][result1: unit]
        t1 = (store t i (access t j)) (store t i result) tt Post1) in
      let (t1, result0, Post2) =
        let (result0, Post2) = (exist_1 [result0: Z]
          (store t0 j result0) = (store t0 j v) v
          (refl_equal ? (store t0 j v))) in
        let Pre4 = Pre2 in
        (exist_2 [t2: (array N Z)][result2: unit]
        t2 = (store t0 j v) (store t0 j result0) tt Post2) in
      (exist_2 [t2: (array N Z)][result1: unit](exchange t2 t i j) t1 
      result0 (swap_po_2 N i j t Pre5 Pre1 v Post3 Pre2 t0 Post1 t1 Post2)) in
    (exist_2 [t1: (array N Z)][result0: unit](exchange t1 t i j) t0 result
    Post4).

