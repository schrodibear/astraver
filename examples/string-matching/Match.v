(**************************************************************************)
(*                                                                        *)
(* Proof of the Knuth-Morris-Pratt Algorithm.                             *)
(*                                                                        *)
(* Jean-Christophe Filliâtre (LRI, Université Paris Sud)                  *)
(* November 1998                                                          *)
(*                                                                        *)
(**************************************************************************)

Require Export WhyArrays.

Implicit Arguments On.


(* Here we define the property (match t1 i1 t2 i2 n) which expresses
 * that the two segments [i1...i1+n-1] of t1 and [i2...i2+n-1] of t2
 * are equal.
 *)

Inductive match [ A:Set; t1:(array A); i1:Z;
                         t2:(array A); i2:Z; n:Z ] : Prop :=
  match_cons :
     `0 <= i1 <= (array_length t1)-n`
  -> `0 <= i2 <= (array_length t2)-n`
  -> ((i:Z) `0 <= i < n` -> #t1[`i1+i`] = #t2[`i2+i`])
  -> (match t1 i1 t2 i2 n).


(* Lemmas about match *)

Require Omega.

Section match_lemmas.

Variable A : Set.
Variable t1 : (array A).
Variable t2 : (array A).

Lemma match_empty :
  (i1,i2:Z)`0 <= i1 <= (array_length t1)`
      	  -> `0 <= i2 <= (array_length t2)`
	  -> (match t1 i1 t2 i2 `0`).
Proof.
Intros i1 i2 Hi1 Hi2.
Apply match_cons. Omega. Omega.
Intros. Absurd `i<0`; Omega.
Save.

Lemma match_right_extension :
  (i1,i2,n:Z)(match t1 i1 t2 i2 n)
      	  -> `i1 <= (array_length t1)-n-1`
	  -> `i2 <= (array_length t2)-n-1`
          -> #t1[`i1+n`]=#t2[`i2+n`]
	  -> (match t1 i1 t2 i2 `n+1`).
Proof.
Intros i1 i2 n Hmatch Hi1 Hi2 Hn.
Elim Hmatch; Intros Hi1' Hi2' Heq.
Apply match_cons.
Omega.
Omega.
Intros i Hi.
Elim (Z_le_lt_eq_dec i n).
Intro. Apply Heq. Omega.
Intro H. Rewrite H. Auto.
Omega.
Save.

Lemma match_contradiction_at_first :
  (i1,i2,n:Z) `0 < n`
         -> ~ (#t1[i1]=#t2[i2])
         -> ~ (match t1 i1 t2 i2 n).
Proof.
Intros i1 i2 n Hn Heq.
Red. Intro Hmatch. Elim Hmatch; Intros.
Absurd #t1[i1]=#t2[i2]; [ Assumption | Idtac ].
Replace i1 with `i1+0`. Replace i2 with `i2+0`.
Apply (H1 `0`).
Omega.
Omega.
Omega.
Save.

Lemma match_contradiction_at_i :
  (i1,i2,i,n:Z) `0 < n`
         -> `0 <= i < n`
         -> ~ (#t1[`i1+i`]=#t2[`i2+i`])
         -> ~ (match t1 i1 t2 i2 n).
Proof.
Intros i1 i2 i n Hn Hi Heq.
Red. Intro Hmatch. Elim Hmatch; Intros.
Absurd #t1[`i1+i`]=#t2[`i2+i`]; [ Assumption | Idtac ].
Apply (H1 i); Omega.
Save.  

Lemma match_right_weakening :
  (i1,i2,n,n':Z)
     (match t1 i1 t2 i2 n)
  -> `n' < n`
  -> (match t1 i1 t2 i2 n').
Proof.
Intros i1 i2 n n' Hmatch Hn.
Elim Hmatch; Intros.
Apply match_cons. Omega. Omega.
Intros i Hi. Apply H1; Omega.
Save.

Lemma match_left_weakening :
  (i1,i2,n,n':Z)
     (match t1 `i1-(n-n')` t2 `i2-(n-n')` n)
  -> `n' < n`
  -> (match t1 i1 t2 i2 n').
Proof.
Intros i1 i2 n n' Hmatch Hn.
Decompose [match] Hmatch.
Apply match_cons. Omega. Omega.
Intros i Hi.
Replace `i1+i` with `i1-(n-n')+(i+(n-n'))`.
Replace `i2+i` with `i2-(n-n')+(i+(n-n'))`.
Apply H1.
Omega. Omega. Omega.
Save.

Lemma match_sym :
  (i1,i2,n:Z) (match t1 i1 t2 i2 n) -> (match t2 i2 t1 i1 n).
Proof.
Intros i1 i2 n Hmatch.
Decompose [match] Hmatch.
Apply match_cons. Omega. Omega.
Intros i Hi. Symmetry.
Apply H1; Omega.
Save.

Variable t3 : (array A).

Lemma match_trans :
  (i1,i2,i3,n:Z)
       (match t1 i1 t2 i2 n)
    -> (match t2 i2 t3 i3 n)
    -> (match t1 i1 t3 i3 n).
Proof.
Intros i1 i2 i3 n H12 H23.
Decompose [match] H12. Decompose [match] H23.
Apply match_cons. Omega. Omega.
Intros i Hi. Apply trans_equal with y := #t2[`i2+i`].
Apply H1; Omega.
Apply H4; Omega.
Save.

Lemma match_left_extension :
  (i,j,n:Z)
  `0 <= i` -> `0 <= j` -> `0 < n` ->
  (access t1 i) = (access t2 j) ->
  (match t1 `i+1` t2 `j+1` `n-1`) ->
  (match t1 i t2 j n).
Proof.
Intros i j n H1 H2 H3 H4 Hmatch.
Decompose [match] Hmatch.
Apply match_cons. Omega. Omega.
Intuition.
Assert `i0=0` \/ `0<i0`. Omega. Intuition.
Subst; Ring `i+0`; Ring `j+0`; Assumption.
Replace `i+i0` with `i+1+(i0-1)`; Try Omega.
Replace `j+i0` with `j+1+(i0-1)`; Try Omega.
Apply H5; Omega.
Save.

End match_lemmas.


  
