(**************************************************************************)
(*                                                                        *)
(* Proof of the Quicksort Algorithm.                                      *)
(*                                                                        *)
(* Jean-Christophe Filliâtre (LRI, Université Paris Sud)                  *)
(* August 1998                                                            *)
(*                                                                        *)
(**************************************************************************)

Require Export Arrays.
Require Exchange.
Require ArrayPermut.

Require Omega.

Implicit Arguments On.


(* Here we define the property "partition_p" which expresses that,
 * on the segment [g,d] of the array t, all elements on the left of p
 * are lesser or equal than t[p] and all elements on the right of p
 * are greater or equal than t[p].
 *
 * So we introduce the properties array_le and array_ge which express
 * that all elements of a segment [g,d] are <= (resp. >=) than a given value
 *)

Inductive array_le [N:Z; t:(array N Z) ; g,d,v:Z] : Prop
  := array_le_cons :
     ((i:Z) `g <= i <= d` -> (Zle #t[i] v))
  -> (array_le t g d v).

Inductive array_ge [N:Z; t:(array N Z) ; g,d,v:Z] : Prop
  := array_ge_cons :
     ((i:Z) `g <= i <= d` -> (Zle v #t[i]))
  -> (array_ge t g d v).

Inductive partition_p [N:Z; t:(array N Z) ; g,d,p:Z] : Prop
  := piv : `g <= p` -> `p <= d`
         -> (array_le t g `p-1` #t[p])
         -> (array_ge t `p+1` d #t[p])
         -> (partition_p t g d p).


(* Lemmas about array_le *)

Lemma array_le_empty :
  (N:Z)(t:(array N Z))(g,d,v:Z)
    `d < g`
    -> (array_le t g d v).
Proof.
Intros N t g d v H.
Constructor. Intros.
Absurd `g<=d`; Omega.
Save.

Lemma array_le_right_extension :
  (N:Z)(t:(array N Z))(g,d,v:Z)
    (array_le t g d v)
    -> (Zle #t[`d+1`] v)
      -> (array_le t g `d+1` v).
Proof.
Intros N t g d v H_le Hv.
Elim H_le; Intros.
Constructor. Intros.
Elim (Z_eq_dec i `d+1`); Intro.
Rewrite a; Assumption.
Apply H; Omega.
Save.

Lemma array_le_exchange :
  (N:Z)(t,t':(array N Z))(g,d,v:Z)(x,y:Z)
    `0 <= g` -> `d < N`
    -> (array_le t g d v)
    -> `d < x <= y`
      -> (exchange t t' x y)
        -> (array_le t' g d v).
Proof.
Intros N t t' g d v x y Hg Hd Hle Hxy Hex.
Elim Hle; Intros. 
Elim Hex; Intros.
Constructor. Intros.
Rewrite <- H4; Try Omega.
Apply H; Assumption.
Save.

(* Lemmas about array_ge *)

Lemma array_ge_empty :
  (N:Z)(t:(array N Z))(g,d,v:Z)
    `d < g`
    -> (array_ge t g d v).
Proof.
Intros N t g d v H.
Constructor. Intros.
Absurd `g<=d`; Omega.
Save.

Lemma array_ge_left_extension :
  (N:Z)(t:(array N Z))(g,d,v:Z)
    (array_ge t g d v)
    -> (Zle v #t[`g-1`])
      -> (array_ge t `g-1` d v).
Proof.
Intros N t g d v H_ge Hv.
Elim H_ge; Intros.
Constructor. Intros.
Elim (Z_eq_dec i `g-1`); Intro.
Rewrite a; Assumption.
Apply H; Omega.
Save.

Lemma array_ge_exchange :
  (N:Z)(t,t':(array N Z))(g,d,v:Z)(x,y:Z)
    `0 <= g` -> `d < N`
    -> (array_ge t g d v)
    -> `x <= y < g`
      -> (exchange t t' x y)
        -> (array_ge t' g d v).
Proof.
Intros N t t' g d v x y Hg Hd Hge Hxy Hex.
Elim Hge; Intros. 
Elim Hex; Intros.
Constructor. Intros.
Rewrite <- H4; Try Omega.
Apply H; Assumption.
Save.


(* Lemmas about partition_p and sub_permut *)

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


Lemma partition_p_permut_left :
  (N:Z)(t,t':(array N Z))(g,d,p:Z)
  `0 <= g` -> `g < d` -> `d < N` -> `g <= p <= d`
  -> (partition_p t g d p)
  -> (sub_permut g (Zpred p) t t')
  -> (partition_p t' g d p).
Proof.
Intros N t t' g d p hyp1 hyp2 hyp3 hyp4 piv_t perm.
Elim piv_t; Intros.
Cut `(Zpred p)<N` ; [ Intro | Unfold Zpred; Omega ].
Generalize (sub_permut_function hyp1 H3 perm). Intro.
Constructor; Try Assumption.
(* array_le *)
Constructor. Intros.
Rewrite <- (sub_permut_eq perm 8!p).
Elim H1; Intros.
Elim (H4 i); Try (Unfold Zpred; Omega). Intros.
Elim H8; Intros.
Elim H9; Intros. Rewrite H11.
Apply H6; Unfold Zpred in H10; Omega.
Unfold Zpred; Omega.
(* array_ge *)
Constructor. Intros.
Rewrite <- (sub_permut_eq perm 8!p).
Rewrite <- (sub_permut_eq perm 8!i).
Elim H2; Intros.
Apply H6; Omega.
Unfold Zpred; Omega.
Unfold Zpred; Omega.
Save.


Lemma partition_p_permut_right :
  (N:Z)(t,t':(array N Z))(g,d,p:Z)
  `0 <= g` -> `g < d` -> `d < N` -> `g <= p <= d`
  -> (partition_p t g d p)
  -> (sub_permut (Zs p) d t t')
  -> (partition_p t' g d p).
Proof.
Intros N t t' g d p hyp1 hyp2 hyp3 hyp4 piv_t perm.
Elim piv_t; Intros.
Cut `0<=(Zs p)` ; [ Intro | Unfold Zpred; Omega ].
Generalize (sub_permut_function H3 hyp3 perm). Intro.
Constructor; Try Assumption.
(* array_le *)
Constructor. Intros.
Rewrite <- (sub_permut_eq perm 8!p).
Rewrite <- (sub_permut_eq perm 8!i).
Elim H1; Intros.
Apply H6; Omega.
Unfold Zs; Omega.
Unfold Zs; Omega.
(* array_ge *)
Constructor. Intros.
Rewrite <- (sub_permut_eq perm 8!p).
Elim H2; Intros.
Elim (H4 i); Try (Unfold Zs; Omega). Intros.
Elim H8; Intros.
Elim H9; Intros. Rewrite H11.
Apply H6; Unfold Zs in H10; Omega.
Unfold Zs; Omega.
Save.
