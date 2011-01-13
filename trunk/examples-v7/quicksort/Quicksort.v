(**************************************************************************)
(*                                                                        *)
(* Proof of the Quicksort Algorithm.                                      *)
(*                                                                        *)
(* Jean-Christophe Filliâtre (LRI, Université Paris Sud)                  *)
(* August 1998                                                            *)
(*                                                                        *)
(**************************************************************************)

Require Why.
Require Partition.

Require Omega.

(* Here we prove the main lemma of quicksort:
 *
 * We have four arrays t0, t1, t2 and t3, and some indexes g,d,p
 * with the following properties
 *
 *                  g           p             d
 *   t0 :  |        |                         |        |
 *   t1 :  |  = t0  |  <= v    |v|    >=v     |  = t0  |
 *   t2 :  |  = t1  |  sorted  |v|    = t1    |  = t1  |
 *   t3 :  |  = t2  |  = t2    |v|   sorted   |  = t2  |
 *
 * and we have to prove that t3 is sorted and is a permutation of t0 
 *)

Lemma quicksort_lemma :
  (t0,t1,t2,t3:(array Z))
  (g,d,p:Z) `0 <= g` -> `g < d` -> `d < (array_length t0)` -> `g <= p <= d`
    -> (partition_p t1 g d p) -> (sub_permut g d t1 t0)
     -> (sorted_array t2 g (Zpred p)) -> (sub_permut g (Zpred p) t2 t1)
       -> (sorted_array t3 (Zs p) d) -> (sub_permut(Zs p) d t3 t2 )
         -> (sorted_array t3 g d) /\ (sub_permut g d t3 t0).
Proof.
Intros t0 t1 t2 t3 g d p H1 H2 H3 H4
  piv_t1 perm_t1 sort_t2 perm_t2 sort_t3 perm_t3.
Generalize (sub_permut_length perm_t1); Intro HL1. 
Generalize (sub_permut_length perm_t2); Intro HL2. 
Generalize (sub_permut_length perm_t3); Intro HL3. 
Rewrite <- HL1 in H3.
Generalize
  (partition_p_permut_left H1 H2 H3 H4 piv_t1 (sub_permut_sym perm_t2)).
  Intro piv_t2.
Rewrite <- HL2 in H3.
Generalize 
  (partition_p_permut_right H1 H2 H3 H4 piv_t2 (sub_permut_sym perm_t3)).
  Intro piv_t3.
Generalize (sub_permut_is_permut perm_t1); Intro.
  Elim (sub_permut_id perm_t1); Intros.
Generalize (sub_permut_is_permut perm_t2); Intro.
  Elim (sub_permut_id perm_t2); Intros.
Generalize (sub_permut_is_permut perm_t3); Intro.
  Elim (sub_permut_id perm_t3); Intros.
Split.
(* sorted_array *)
Unfold sorted_array. Intros.
Elim (Z_lt_ge_dec x `p-1`); Intros.
(* x < p-1 *)
Unfold array_id in H10.
Rewrite (H10 x); Try Omega. Rewrite (H10 `x+1`); Try Omega.
Unfold sorted_array in sort_t2.
Apply sort_t2; Unfold Zpred; Omega.
Elim (Z_lt_ge_dec x p); Intros.
(* x = p-1 *)
Elim piv_t3; Intros.
Elim H17; Intros.
Cut `x+1=p`. Intro Heq. Rewrite Heq.
Apply H19; Omega.
Omega.
Elim (Z_lt_ge_dec x `p+1`); Intros.
(* x = p *)
Elim piv_t3; Intros.
Elim H18; Intros.
Cut `x=p`. Intro Heq. Rewrite Heq.
Apply H19; Omega.
Omega.
(* x > p *)
Unfold sorted_array in sort_t3.
Apply sort_t3; Unfold Zs; Omega.

(* sub_permut *)
Apply sub_permut_trans with t':=t2.
Elim (Z_le_gt_dec (Zs p) d); Intro.
Apply sub_permut_extension with g:=(Zs p) d:=d; Try Omega.
Assumption.
Apply sub_permut_void with g:=(Zs p) d:=d; Try Omega.
Assumption.
Apply sub_permut_trans with t':=t1.
Elim (Z_le_gt_dec g (Zpred p)); Intro.
Apply sub_permut_extension with g:=g d:=(Zpred p); Try (Unfold Zpred;Omega).
Assumption.
Apply sub_permut_void with g:=g d:=(Zpred p); Try (Unfold Zpred;Omega).
Omega.
Assumption.
Assumption.
Save.


(* The trivial case, when the segment of the array contains at most
 * one element.
 *)

Lemma quicksort_trivial :
  (t:(array Z))
  (g,d:Z) `0 <= g` -> `g >= d` -> `d < (array_length t)`
    -> (sorted_array t g d) /\ (sub_permut g d t t).
Proof.
Intros t g d H1 H2 H3.
Split.
Unfold sorted_array.
Intros.
(Absurd `x < d`; Omega).
Auto with datatypes.
Save.

    
