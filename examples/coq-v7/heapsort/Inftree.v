(**************************************************************************)
(*                                                                        *)
(* Proof of the Heapsort Algorithm.                                       *)
(*                                                                        *)
(* Jean-Christophe Filliâtre (LRI, Université Paris Sud)                  *)
(* March 1999                                                             *)
(*                                                                        *)
(**************************************************************************)

Require ZArith.
Require Why.
Require Omega.

Require heap.

Implicit Arguments On.

(* We will also need another property about a heap, which is to have
 * all his elements smaller or equal than a given value v.
 *
 * It is expressed by the predicate (inftree t n v k), inductively
 * defined as follows:
 *)

Inductive inftree [t:(array Z); n,v:Z] : Z -> Prop :=
  inftree_cons : (k:Z)
      `0 <= k <= n` 
   -> `(access t k) <= v`
   -> (`2*k+1 <= n` -> (inftree t n v `2*k+1`))
   -> (`2*k+2 <= n` -> (inftree t n v `2*k+2`))
   -> (inftree t n v k).

(* Some lemmas about inftree *)

Lemma inftree_1 : (t:(array Z))(n,v,k:Z)
  (inftree t n v k) -> `(access t k) <= v`.
Proof.
Intros t n v k H. Elim H; Auto.
Save.

Lemma inftree_id : (t1,t2:(array Z))(n,v,k:Z)
    (inftree t1 n v k)
 -> ((i:Z) `k <= i <= n` -> `(access t1 i) = (access t2 i)`)
 -> (inftree t2 n v k).
Proof.
Intros t1 t2 n v k H. Elim H; Intros.
Apply inftree_cons.
Assumption.

Rewrite <- (H6 k0). Assumption. Omega'.

Intro. Apply H3. Assumption.
Intros i Hi. Apply H6; Omega'.

Intro. Apply H5. Assumption.
Intros i Hi. Apply H6; Omega'.
Save.

Lemma inftree_2 : (t1,t2:(array Z))(n,v,k,j:Z)
    `n < (array_length t1)`
 -> (inftree t1 n v j) 
 -> (exchange t2 t1 k j)
 -> `k < j`
 -> `(access t1 k) <= (access t1 j)`
 -> (inftree t2 n v j).
Proof.
Intros t1 t2 n v k j Hn H. Case H.
Intros.
Apply inftree_cons.
Assumption.
Decompose [exchange] H4. Omega'.

Intro. Apply inftree_id with t1:=t1. Auto.
Decompose [exchange] H4.
Intros i Hi. Symmetry. Apply H13.
Omega'. Omega'. Omega'.

Intro. Apply inftree_id with t1:=t1. Auto.
Decompose [exchange] H4.
Intros i Hi. Symmetry. Apply H13.
Omega'. Omega'. Omega'.
Save.

Lemma inftree_trans : (t:(array Z))(n,k,v,v':Z)
  `v <= v'` -> (inftree t n v k) -> (inftree t n v' k).
Proof.
Intros t n k v v' Hvv' H.
(Elim H; Intros).
Apply inftree_cons.
Assumption. Omega'. Auto. Auto.
Save.

Lemma inftree_3 : (t:(array Z))(n,k:Z)
  (heap t n k) -> (inftree t n #t[k] k).
Proof.
Intros t n k H. Elim H; Intros.
Apply inftree_cons.
Assumption.
Auto with zarith.
Intro. Apply inftree_trans with v:=#t[`2*k0+1`] v':=#t[k0].  
Omega'. Auto.
Intro. Apply inftree_trans with v:=#t[`2*k0+2`] v':=#t[k0].  
Omega'. Auto.
Save.

Lemma inftree_all : (t:(array Z))(n,v:Z)
  (inftree t n v `0`) -> (i:Z)`0 <= i <= n` -> (inftree t n v i).
Proof.
Intros t n v H0 i H.
Generalize H.
Pattern i.
Apply heap_induction.
Auto.

Intros.
Elim (Z_le_gt_dec k n).
Intro.
Generalize H1 a.
(Case H2; Intros).
Intuition.

Split.
(Intro; Apply H5; Omega).
(Intro; Apply H6; Omega).

Intro. (Split; Intro; Absurd `k > n`; Omega).
Intuition.
Save.

Lemma inftree_0_right : (t:(array Z))(n,v:Z)
  (inftree t n v `0`) -> (i:Z)`0 <= i <= n` -> `(access t i) <= v`.
Proof.
Intros t n v H.
Generalize (inftree_all H).
Intros.
Apply inftree_1 with n:=n.
Exact (H0 i H1).
Save.

Lemma inftree_0_left : (t:(array Z))(n,v:Z)
  `0 <= n` -> 
  ((i:Z)`0 <= i <= n` -> `(access t i) <= v`) -> (inftree t n v `0`).
Proof.
Intros.
Cut (i:Z)`0 <= i <= n`->(inftree t n v i).
Intro.
(Apply H1; Omega).

Intros i Hi. Generalize Hi.
Replace i with `n-(n-i)`.
Pattern `n-i`.
Apply Z_lt_induction.
Intros.
Apply inftree_cons.
Assumption.

(Apply H0; Omega).

Intro.
Replace `2*(n-x)+1` with `n-(n-(2*(n-x)+1))`.
(Apply H1; Omega).
Omega.

Intro.
Replace `2*(n-x)+2` with `n-(n-(2*(n-x)+2))`.
(Apply H1; Omega).
Omega.

Omega. Omega.
Save.

Lemma inftree_exchange : (t1,t2:(array Z))(n,v:Z)
    `n < (array_length t1)`
 -> (inftree t1 n v `0`) 
 -> (exchange t2 t1 `0` n)
 -> (inftree t2 n v `0`).
Proof.
Intros.
Apply inftree_0_left.
Decompose [exchange] H1.
Omega.

Generalize (inftree_0_right H0).
Intros.
Decompose [exchange] H1.
(Elim (Z_lt_ge_dec `0` i); Intro).
(Elim (Z_lt_ge_dec i n); Intro).
Rewrite (H9 i).
(Apply H2; Omega).

Omega. Omega. Omega.

Replace i with n.
Rewrite H8.
(Apply H2; Omega).

Omega.

Replace i with `0`.
Rewrite H7.
(Apply H2; Omega).

Omega.
Save.

Lemma inftree_weakening : (t:(array Z))(n,v,k:Z)
  `1 <= n < (array_length t)` -> (inftree t n v k) -> `k <= n-1` -> (inftree t `n-1` v k).
Proof.
Intros t n v k Hn Htree.
Elim Htree; Intros.
Apply inftree_cons.
Omega.
Assumption.
Intro; Apply H2; Omega.
Intro; Apply H4; Omega.
Save.
