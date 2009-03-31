
Require Import Why.
Require Import Omega.







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

(*Why predicate*) Definition exchange (A118:Set) (a1:(array A118)) (a2:(array A118)) (i:Z) (j:Z)
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

(*Why predicate*) Definition permutation (A127:Set) (a1:(array A127)) (a2:(array A127))
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

(*Why type*) Definition foo: Set.
Admitted.

















(*Why*) Inductive ET_E1 (T:Set) : Set :=
          | Val_E1 : T -> ET_E1 T
          | Exn_E1 : ET_E1 T.

(*Why*) Definition post_E1 (T:Set) (P:Prop) (Q:T -> Prop)
          (x:ET_E1 T) :=
          match x with
          | Val_E1 v => Q v
          | Exn_E1 => P
          end.

(*Why*) Implicit Arguments post_E1.

(*Why*) Inductive ET_E2 (T:Set) : Set :=
          | Val_E2 : T -> ET_E2 T
          | Exn_E2 : Z -> ET_E2 T.

(*Why*) Definition post_E2 (T:Set) (P:Z -> Prop) (Q:T -> Prop)
          (x:ET_E2 T) :=
          match x with
          | Val_E2 v => Q v
          | Exn_E2 v => P v
          end.

(*Why*) Implicit Arguments post_E2.

(*Why*) Inductive ET_E3 (T:Set) : Set :=
          | Val_E3 : T -> ET_E3 T
          | Exn_E3 : foo -> ET_E3 T.

(*Why*) Definition post_E3 (T:Set) (P:foo -> Prop) (Q:T -> Prop)
          (x:ET_E3 T) :=
          match x with
          | Val_E3 v => Q v
          | Exn_E3 v => P v
          end.

(*Why*) Implicit Arguments post_E3.



























(* Why obligation from file "good/all.mlw", line 34, characters 13-22: *)
(*Why goal*) Lemma p2_po_1 : 
  ~False.
Proof.
tauto.
Save.



(* Why obligation from file "good/all.mlw", line 35, characters 13-26: *)
(*Why goal*) Lemma p3_po_1 : 
  (True /\ True).
Proof.
tauto.
Save.



(* Why obligation from file "good/all.mlw", line 36, characters 13-26: *)
(*Why goal*) Lemma p4_po_1 : 
  (True \/ False).
Proof.
tauto.
Save.



(* Why obligation from file "good/all.mlw", line 37, characters 13-31: *)
(*Why goal*) Lemma p5_po_1 : 
  (False \/ ~False).
Proof.
tauto.
Save.



(* Why obligation from file "good/all.mlw", line 38, characters 13-30: *)
(*Why goal*) Lemma p6_po_1 : 
  ((True -> ~False)).
Proof.
tauto.
Save.





(* Why obligation from file "good/all.mlw", line 40, characters 13-39: *)
(*Why goal*) Lemma p8_po_1 : 
  (True /\ (forall (x:Z), x = x)).
Proof.
intuition.
Save.


























(* Why obligation from file "good/all.mlw", line 58, characters 10-13: *)
(*Why goal*) Lemma ar6_po_1 : 
  1 <> 0.
Proof.
intuition.
Save.























(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma c2_po_1 : 
  forall (v1: bool),
  (if v1 then True else True).
Proof.
destruct v1; intuition.
Save.

(* Why obligation from file "good/all.mlw", line 101, characters 40-45: *)
(*Why goal*) Lemma arr1_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 1),
  (0 <= 0 /\ 0 < (array_length v6)).
Proof.
intuition.
Save.



(* Why obligation from file "good/all.mlw", line 102, characters 40-47: *)
(*Why goal*) Lemma arr2_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 4),
  (0 <= (1 + 2) /\ (1 + 2) < (array_length v6)).
Proof.
intuition.
Save.



(* Why obligation from file "good/all.mlw", line 103, characters 51-58: *)
(*Why goal*) Lemma arr3_po_1 : 
  forall (v4: Z),
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 1 /\ v4 = 0),
  (0 <= v4 /\ v4 < (array_length v6)).
Proof.
intuition.
Save.



(* Why obligation from file "good/all.mlw", line 104, characters 58-63: *)
(*Why goal*) Lemma arr4_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 10 /\ (access v6 0) = 9),
  (0 <= 0 /\ 0 < (array_length v6)).
Proof.
intuition.
Save.


(* Why obligation from file "good/all.mlw", line 104, characters 55-64: *)
(*Why goal*) Lemma arr4_po_2 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 10 /\ (access v6 0) = 9),
  forall (HW_2: 0 <= 0 /\ 0 < (array_length v6)),
  forall (result: Z),
  forall (HW_3: result = (access v6 0)),
  (0 <= result /\ result < (array_length v6)).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 106, characters 40-50: *)
(*Why goal*) Lemma arr5_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 1),
  (0 <= 0 /\ 0 < (array_length v6)).
Proof.
intuition.
Save.



(* Why obligation from file "good/all.mlw", line 107, characters 40-54: *)
(*Why goal*) Lemma arr6_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 4),
  (0 <= (1 + 2) /\ (1 + 2) < (array_length v6)).
Proof.
intuition.
Save.



(* Why obligation from file "good/all.mlw", line 108, characters 58-63: *)
(*Why goal*) Lemma arr7_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 10 /\ (access v6 0) = 9),
  (0 <= 0 /\ 0 < (array_length v6)).
Proof.
intuition.
Save.





(* Why obligation from file "good/all.mlw", line 108, characters 55-69: *)
(*Why goal*) Lemma arr7_po_2 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 10 /\ (access v6 0) = 9),
  forall (HW_2: 0 <= 0 /\ 0 < (array_length v6)),
  forall (result: Z),
  forall (HW_3: result = (access v6 0)),
  (0 <= result /\ result < (array_length v6)).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 113, characters 48-54: *)
(*Why goal*) Lemma fc3_po_1 : 
  0 >= 0.
Proof.
intuition.
Save.





(* Why obligation from file "good/all.mlw", line 121, characters 51-59: *)
(*Why goal*) Lemma an2_po_1 : 
  forall (v4: Z),
  forall (HW_1: v4 >= 0),
  forall (v4_0: Z),
  forall (HW_2: v4_0 = (v4 + 1)),
  v4_0 > v4.
Proof.
intuition.
Save.









