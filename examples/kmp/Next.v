(**************************************************************************)
(*                                                                        *)
(* Proof of the Knuth-Morris-Pratt Algorithm.                             *)
(*                                                                        *)
(* Jean-Christophe Filliâtre (LRI, Université Paris Sud)                  *)
(* November 1998                                                          *)
(*                                                                        *)
(**************************************************************************)

Require Match.
Require ZArithRing.
Require Omega.

Implicit Arguments On.

(* next[j] is the maximal n < j such that the n first elements of p
 * match the n last elemnts of p[0..j-1]
 *
 *          _______ ____ j____
 *     p = |_______|abcd|_____|
 *                  ____ n___________
 *                 |abcd|____________|
 *
 * This property is expressed by the predicate (Next p j n).
 *)

Section next_prop.

Variable A : Set.
Variable M : Z.
Variable p : (array M A).

(* Definition *)
 
Inductive Next [j,n:Z] : Prop :=
  Next_cons : 
     `0 <= n < j`
  -> (match p `j-n` p `0` n)
  -> ((z:Z)`n < z < j` -> ~(match p `j-z` p `0` z))   (* n is maximal *)
  -> (Next j n).


(* Some properties of the predicate Next *)

Variable N : Z.
Variable a : (array N A).

Lemma next_iteration :
  (i,j,n:Z)
         `0 < j < M`
      -> `j <= i <= N`
      -> (match a `i-j` p `0` j)
      -> (Next j n)
      -> (match a `i-n` p `0` n).
Proof.
Intros i j n Hj Hi Hmatch Hnext.
Elim Hnext; Intros.
Apply match_cons. Omega. Omega.
Intros i0 Hi0.
Apply trans_equal with y := #p[`j-n+i0`].
Elim Hmatch; Intros.
Replace `i-n+i0` with `i-j+(j-n+i0)`.
Replace `j-n+i0` with `0+(j-n+i0)`.
Apply H4.
Omega. Omega. Omega.
Elim H0; Intros.
Apply H4.
Omega.
Save.


Lemma next_is_maximal :
  (i,j,n,k:Z)
        `0 < j < M`
     -> `j <= i <= N`
     -> `i-j < k < i-n`
     -> (match a `i-j` p `0` j)
     -> (Next j n)
     -> ~(match a k p `0` M).
Proof.
Intros i j n k Hj Hi Hk Hmatch Hnext.
Red. Intro Hmax.
Elim Hnext; Intros.
Absurd (match p `j-(i-k)` p `0` `i-k`).
Apply H1; Omega.
Apply match_trans with t2 := a i2 := k.
Apply match_sym.
Apply match_left_weakening with n := j.
Ring `k-(j-(i-k))`. Ring `j-(i-k)-(j-(i-k))`. Assumption.
Omega.
Apply match_right_weakening with n := M.
Assumption.
Omega.
Save.

Lemma next_1_0 : `1 <= M` -> (Next `1` `0`).
Proof.
Intro HM.
Apply Next_cons. 
Omega.
Apply match_empty; Omega.
Intros z Hz. Absurd `0 < z`; Omega.
Save.

End next_prop.
