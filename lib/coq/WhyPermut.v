(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(* $Id: WhyPermut.v,v 1.2 2002-08-29 07:45:18 filliatr Exp $ *)

Require WhyArrays.
Require Omega.

Set Implicit Arguments.

(****************************************************************************)
(*                   Exchange of two elements in an array                   *)
(*                        Definition and properties                         *)
(****************************************************************************)

(* Definition *)

Inductive exchange [n:Z; A:Set; t,t':(array n A); i,j:Z] : Prop :=
  exchange_c :
    `0<=i<n` -> `0<=j<n` ->
    (#t[i] = #t'[j]) ->
    (#t[j] = #t'[i]) ->
    ((k:Z)`0<=k<n` -> `k<>i` -> `k<>j` -> #t[k] = #t'[k]) ->
    (exchange t t' i j).
    
(* Properties about exchanges *)

Lemma exchange_1 : (n:Z)(A:Set)(t:(array n A))
  (i,j:Z) `0<=i<n` -> `0<=j<n` ->
  (access (store (store t i #t[j]) j #t[i]) i) = #t[j].
Proof.
Intros n A t i j H_i H_j.
Case (dec_eq j i).
Intro eq_i_j. Rewrite eq_i_j.
Auto with datatypes.
Intro not_j_i.
Rewrite (store_def_2 (store t i #t[j]) #t[i] H_j H_i not_j_i).
Auto with datatypes.
Save.

Hints Resolve exchange_1 : v62 datatypes.


Lemma exchange_proof :
  (n:Z)(A:Set)(t:(array n A))
  (i,j:Z) `0<=i<n` -> `0<=j<n` ->
  (exchange (store (store t i (access t j)) j (access t i)) t i j).
Proof.
Intros n A t i j H_i H_j.
Apply exchange_c; Auto with datatypes.
Intros k H_k not_k_i not_k_j.
Cut ~j=k; Auto with datatypes. Intro not_j_k.
Rewrite (store_def_2 (store t i (access t j)) (access t i) H_j H_k not_j_k).
Auto with datatypes.
Save.

Hints Resolve exchange_proof : v62 datatypes.


Lemma exchange_sym :
  (n:Z)(A:Set)(t,t':(array n A))(i,j:Z)
  (exchange t t' i j) -> (exchange t' t i j).
Proof.
Intros n A t t' i j H1.
Elim H1. Clear H1. Intros.
Constructor 1; Auto with datatypes.
Intros. Rewrite (H3 k); Auto with datatypes.
Save.

Hints Resolve exchange_sym : v62 datatypes.


Lemma exchange_id :
  (n:Z)(A:Set)(t,t':(array n A))(i,j:Z)
  (exchange t t' i j) -> 
  i=j ->
  (k:Z) `0 <= k < n` -> (access t k)=(access t' k).
Proof.
Intros n A t t' i j Hex Heq k Hk.
Elim Hex. Clear Hex. Intros.
Rewrite Heq in H1. Rewrite Heq in H2.
Case (Z_eq_dec k j). 
  Intro Heq'. Rewrite Heq'. Assumption.
  Intro Hnoteq. Apply (H3 k); Auto with datatypes. Rewrite Heq. Assumption.
Save.

Hints Resolve exchange_id : v62 datatypes.


(****************************************************************************)
(*                    Permutations of elements in arrays                    *)
(*                        Definition and properties                         *)
(****************************************************************************)

(* We define "permut" as the smallest equivalence relation which contains
 * transpositions i.e. exchange of two elements.
 *)

Inductive permut [n:Z; A:Set] : (array n A)->(array n A)->Prop :=
    exchange_is_permut : 
      (t,t':(array n A))(i,j:Z)(exchange t t' i j) -> (permut t t')
  | permut_refl : 
      (t:(array n A))(permut t t)
  | permut_sym : 
      (t,t':(array n A))(permut t t') -> (permut t' t)
  | permut_trans : 
      (t,t',t'':(array n A))
      (permut t t') -> (permut t' t'') -> (permut t t'').

Hints Resolve exchange_is_permut permut_refl permut_sym permut_trans : v62 datatypes.

(* We also define the permutation on a segment of an array, "sub_permut",
 * the other parts of the array being unchanged
 *
 * One again we define it as the smallest equivalence relation containing
 * transpositions on the given segment.
 *)

Inductive sub_permut [n:Z; A:Set; g,d:Z] : (array n A)->(array n A)->Prop :=
    exchange_is_sub_permut : 
      (t,t':(array n A))(i,j:Z)`g <= i <= d` -> `g <= j <= d`
      -> (exchange t t' i j) -> (sub_permut g d t t')
  | sub_permut_refl : 
      (t:(array n A))(sub_permut g d t t)
  | sub_permut_sym : 
      (t,t':(array n A))(sub_permut g d t t') -> (sub_permut g d t' t)
  | sub_permut_trans : 
      (t,t',t'':(array n A))
      (sub_permut g d t t') -> (sub_permut g d t' t'') 
      -> (sub_permut g d t t'').

Hints Resolve exchange_is_sub_permut sub_permut_refl sub_permut_sym sub_permut_trans
  : v62 datatypes.

Lemma sub_permut_function :
  (N:Z)(t,t':(array N Z))(g,d:Z)
  `0 <= g` -> `d < N`
  -> (sub_permut g d t t')
  -> (i:Z) `g <= i <= d`
    -> (EX j:Z | `g <= j <= d` /\ #t[i]=#t'[j])
    /\ (EX j:Z | `g <= j <= d` /\ #t'[i]=#t[j]).
Proof.
Intros N t t' g d hyp1 hyp2.
Induction 1; Intros.
(* 1. exchange *)
Elim H2; Intros.
Elim (Z_eq_dec i0 i); Intros.
(* i0 = i *)
Split ; [ Exists j | Exists j ].
Split; [ Assumption | Rewrite a; Assumption ].
Split; [ Assumption | Rewrite a; Symmetry; Assumption ].
(* i0 <> i *)
Elim (Z_eq_dec i0 j); Intros.
(* i0 = j *)
Split ; [ Exists i | Exists i ].
Split; [ Assumption | Rewrite a; Assumption ].
Split; [ Assumption | Rewrite a; Symmetry; Assumption ].
(* i0 <> j *)
Split ; [ Exists i0 | Exists i0 ].
Split; [ Assumption | Apply H8; Omega ].
Split; [ Assumption | Symmetry; Apply H8; Omega ].

(* 2. refl *)
Split ; [ Exists i | Exists i].
Split; [ Assumption | Trivial ].
Split; [ Assumption | Trivial ].

(* 3. sym *)
Elim (H1 i H2). Auto.

(* 4. trans *)
Split.

Elim (H1 i H4). Intros.
Elim H5; Intros.
Elim H7; Intros.
Elim (H3 x H8). Intros.
Elim H10; Intros.
Elim H12; Intros.
Exists x0. Split ; [ Assumption | Idtac ].
Elim H7; Intros.
Exact (trans_eq Z (access t0 i) (access t'0 x) (access t'' x0) H16 H14).

Elim (H3 i H4). Intros.
Elim H6; Intros.
Elim H7; Intros.
Elim (H1 x H8). Intros.
Elim H11; Intros.
Elim H12; Intros.
Exists x0. Split ; [ Assumption | Idtac ].
Elim H7; Intros.
Exact (trans_eq Z (access t'' i) (access t'0 x) (access t0 x0) H16 H14).
Save.

(* To express that some parts of arrays are equal we introduce the
 * property "array_id" which says that a segment is the same on two
 * arrays.
 *)

Definition array_id := [n:Z][A:Set][t,t':(array n A)][g,d:Z]
  (i:Z) `g <= i <= d` -> #t[i] = #t'[i].

(* array_id is an equivalence relation *)

Lemma array_id_refl : 
  (n:Z)(A:Set)(t:(array n A))(g,d:Z)
  (array_id t t g d).
Proof.
Unfold array_id.
Auto with datatypes.
Save.

Hints Resolve array_id_refl : v62 datatypes.

Lemma array_id_sym :
  (n:Z)(A:Set)(t,t':(array n A))(g,d:Z)
  (array_id t t' g d)
  -> (array_id t' t g d).
Proof.
Unfold array_id. Intros.
Symmetry; Auto with datatypes.
Save.

Hints Resolve  array_id_sym : v62 datatypes.

Lemma array_id_trans :
  (n:Z)(A:Set)(t,t',t'':(array n A))(g,d:Z)
  (array_id t t' g d)
  -> (array_id t' t'' g d)
    -> (array_id t t'' g d).
Proof.
Unfold array_id. Intros.
Apply trans_eq with y:=#t'[i]; Auto with datatypes.
Save.

Hints Resolve array_id_trans: v62 datatypes.

(* Outside the segment [g,d] the elements are equal *)

Lemma sub_permut_id :
  (n:Z)(A:Set)(t,t':(array n A))(g,d:Z)
  (sub_permut g d t t') ->
  (array_id t t' `0` `g-1`) /\ (array_id t t' `d+1` `n-1`).
Proof.
Intros n A t t' g d. Induction 1; Intros.
Elim H2; Intros.
Unfold array_id; Split; Intros.
Apply H7; Omega.
Apply H7; Omega.
Auto with datatypes.
Decompose [and] H1; Auto with datatypes.
Decompose [and] H1; Decompose [and] H3; EAuto with datatypes.
Save.

Hints Resolve sub_permut_id.

Lemma sub_permut_eq :
  (n:Z)(A:Set)(t,t':(array n A))(g,d:Z)
  (sub_permut g d t t') ->
  (i:Z) (`0<=i<g` \/ `d<i<n`) -> #t[i]=#t'[i].
Proof.
Intros n A t t' g d Htt' i Hi.
Elim (sub_permut_id Htt'). Unfold array_id. 
Intros.
Elim Hi; [ Intro; Apply H; Omega | Intro; Apply H0; Omega ].
Save.

(* sub_permut is a particular case of permutation *)

Lemma sub_permut_is_permut :
  (n:Z)(A:Set)(t,t':(array n A))(g,d:Z)
  (sub_permut g d t t') ->
  (permut t t').
Proof.
Intros n A t t' g d. Induction 1; Intros; EAuto with datatypes.
Save.

Hints Resolve sub_permut_is_permut.

(* If we have a sub-permutation on an empty segment, then we have a 
 * sub-permutation on any segment.
 *)

Lemma sub_permut_void :
  (N:Z)(A:Set)(t,t':(array N A))
  (g,g',d,d':Z) `d < g`
   -> (sub_permut g d t t') -> (sub_permut g' d' t t').
Proof.
Intros N A t t' g g' d d' Hdg.
(Induction 1; Intros).
(Absurd `g <= d`; Omega).
Auto with datatypes.
Auto with datatypes.
EAuto with datatypes.
Save.

(* A sub-permutation on a segment may be extended to any segment that
 * contains the first one.
 *)

Lemma sub_permut_extension :
  (N:Z)(A:Set)(t,t':(array N A))
  (g,g',d,d':Z) `g' <= g` -> `d <= d'`
   -> (sub_permut g d t t') -> (sub_permut g' d' t t').
Proof.
Intros N A t t' g g' d d' Hgg' Hdd'.
(Induction 1; Intros).
Apply exchange_is_sub_permut with i:=i j:=j; [ Omega | Omega | Assumption ].
Auto with datatypes.
Auto with datatypes.
EAuto with datatypes.
Save.
