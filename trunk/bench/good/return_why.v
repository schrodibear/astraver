
Require Import Why.


(*Why type*) Definition farray: Set ->Set.
Admitted.

(*Why logic*) Definition access : forall (A1:Set), (array A1) -> Z -> A1.
Admitted.
Implicit Arguments access.

(*Why logic*) Definition update :
  forall (A1:Set), (array A1) -> Z -> A1 -> (array A1).
Admitted.
Implicit Arguments update.

(*Why axiom*) Lemma access_update :
  forall (A1:Set),
  (forall (a:(array A1)),
   (forall (i:Z), (forall (v:A1), (access (update a i v) i) = v))).
Admitted.

(*Why axiom*) Lemma access_update_neq :
  forall (A1:Set),
  (forall (a:(array A1)),
   (forall (i:Z),
    (forall (j:Z),
     (forall (v:A1), (i <> j -> (access (update a i v) j) = (access a j)))))).
Admitted.

(*Why logic*) Definition array_length : forall (A1:Set), (array A1) -> Z.
Admitted.
Implicit Arguments array_length.

(*Why predicate*) Definition sorted_array  (t:(array Z)) (i:Z) (j:Z)
  := (forall (k1:Z),
      (forall (k2:Z),
       ((i <= k1 /\ k1 <= k2) /\ k2 <= j -> (access t k1) <= (access t k2)))).

(*Why predicate*) Definition exchange (A87:Set) (a1:(array A87)) (a2:(array A87)) (i:Z) (j:Z)
  := (array_length a1) = (array_length a2) /\
     (access a1 i) = (access a2 j) /\ (access a2 i) = (access a1 j) /\
     (forall (k:Z), (k <> i /\ k <> j -> (access a1 k) = (access a2 k))).
Implicit Arguments exchange.

(*Why logic*) Definition permut :
  forall (A1:Set), (array A1) -> (array A1) -> Z -> Z -> Prop.
Admitted.
Implicit Arguments permut.

(*Why axiom*) Lemma permut_refl :
  forall (A1:Set),
  (forall (t:(array A1)), (forall (l:Z), (forall (u:Z), (permut t t l u)))).
Admitted.

(*Why axiom*) Lemma permut_sym :
  forall (A1:Set),
  (forall (t1:(array A1)),
   (forall (t2:(array A1)),
    (forall (l:Z), (forall (u:Z), ((permut t1 t2 l u) -> (permut t2 t1 l u)))))).
Admitted.

(*Why axiom*) Lemma permut_trans :
  forall (A1:Set),
  (forall (t1:(array A1)),
   (forall (t2:(array A1)),
    (forall (t3:(array A1)),
     (forall (l:Z),
      (forall (u:Z),
       ((permut t1 t2 l u) -> ((permut t2 t3 l u) -> (permut t1 t3 l u)))))))).
Admitted.

(*Why axiom*) Lemma permut_exchange :
  forall (A1:Set),
  (forall (a1:(array A1)),
   (forall (a2:(array A1)),
    (forall (l:Z),
     (forall (u:Z),
      (forall (i:Z),
       (forall (j:Z),
        (l <= i /\ i <= u ->
         (l <= j /\ j <= u -> ((exchange a1 a2 i j) -> (permut a1 a2 l u)))))))))).
Admitted.

(*Why axiom*) Lemma exchange_upd :
  forall (A1:Set),
  (forall (a:(array A1)),
   (forall (i:Z),
    (forall (j:Z),
     (exchange a (update (update a i (access a j)) j (access a i)) i j)))).
Admitted.

(*Why axiom*) Lemma permut_weakening :
  forall (A1:Set),
  (forall (a1:(array A1)),
   (forall (a2:(array A1)),
    (forall (l1:Z),
     (forall (r1:Z),
      (forall (l2:Z),
       (forall (r2:Z),
        ((l1 <= l2 /\ l2 <= r2) /\ r2 <= r1 ->
         ((permut a1 a2 l2 r2) -> (permut a1 a2 l1 r1))))))))).
Admitted.

(*Why axiom*) Lemma permut_eq :
  forall (A1:Set),
  (forall (a1:(array A1)),
   (forall (a2:(array A1)),
    (forall (l:Z),
     (forall (u:Z),
      (l <= u ->
       ((permut a1 a2 l u) ->
        (forall (i:Z), (i < l \/ u < i -> (access a2 i) = (access a1 i))))))))).
Admitted.

(*Why predicate*) Definition permutation (A96:Set) (a1:(array A96)) (a2:(array A96))
  := (permut a1 a2 0 ((array_length a1) - 1)).
Implicit Arguments permutation.

(*Why axiom*) Lemma array_length_update :
  forall (A1:Set),
  (forall (a:(array A1)),
   (forall (i:Z),
    (forall (v:A1), (array_length (update a i v)) = (array_length a)))).
Admitted.

(*Why axiom*) Lemma permut_array_length :
  forall (A1:Set),
  (forall (a1:(array A1)),
   (forall (a2:(array A1)),
    (forall (l:Z),
     (forall (u:Z),
      ((permut a1 a2 l u) -> (array_length a1) = (array_length a2)))))).
Admitted.

(*Why logic*) Definition N : Z.
Admitted.

(* Why obligation from file "return.mlw", line 16, characters 18-24: *)
(*Why goal*) Lemma p_po_1 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  0 <= i.
Proof.
intuition.
Save.

(* Why obligation from file "return.mlw", line 18, characters 9-14: *)
(*Why goal*) Lemma p_po_2 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_4: i0 < N),
  (0 <= i0 /\ i0 < (array_length t)).
Proof.
intuition.
Save.

(* Why obligation from file "return.mlw", line 25, characters 4-36: *)
(*Why goal*) Lemma p_po_3 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_4: i0 < N),
  forall (HW_5: 0 <= i0 /\ i0 < (array_length t)),
  forall (result: Z),
  forall (HW_6: result = (access t i0)),
  forall (HW_7: result = 0),
  forall (HW_8: 0 <= i0 /\ i0 < N),
  (access t i0) = 0.
Proof.
intuition.
Save.

(* Why obligation from file "return.mlw", line 16, characters 18-24: *)
(*Why goal*) Lemma p_po_4 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_4: i0 < N),
  forall (HW_5: 0 <= i0 /\ i0 < (array_length t)),
  forall (result: Z),
  forall (HW_6: result = (access t i0)),
  forall (HW_9: result <> 0),
  forall (i1: Z),
  forall (HW_10: i1 = (i0 + 1)),
  0 <= i1.
Proof.
intuition.
Save.

(* Why obligation from file "return.mlw", line 17, characters 16-21: *)
(*Why goal*) Lemma p_po_5 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_4: i0 < N),
  forall (HW_5: 0 <= i0 /\ i0 < (array_length t)),
  forall (result: Z),
  forall (HW_6: result = (access t i0)),
  forall (HW_9: result <> 0),
  forall (i1: Z),
  forall (HW_10: i1 = (i0 + 1)),
  (Zwf 0 (N - i1) (N - i0)).
Proof.
intuition.
Save.

(* Why obligation from file "return.mlw", line 25, characters 4-36: *)
(*Why goal*) Lemma p_po_6 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_11: i0 >= N),
  forall (HW_12: 0 <= N /\ N < N),
  (access t N) = 0.
Proof.
intuition.
Save.

