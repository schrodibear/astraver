(**************************************************************************)
(*                                                                        *)
(* Proof of the Heapsort Algorithm.                                       *)
(*                                                                        *)
(* Jean-Christophe Filliâtre (LRI, Université Paris Sud)                  *)
(* March 1999                                                             *)
(*                                                                        *)
(**************************************************************************)

Require ZArith.
Require Arrays.
Require ArrayPermut.
Require Omega.

Tactic Definition Omega' := Abstract Omega.

Implicit Arguments On.

(* First we define the heap structure.
 * 
 * The heap is represented in an array[0..N-1] with the two sons
 * of the ``root'' i at indexes 2i+1 and 2i+2.
 * 
 * A sub_array t[k..n] is a heap if the following conditions are satisfied:
 *  - t[k] <= t[2k+1]             (if 2k+1 <= n)
 *  - t[2k+1..n] is itself a heap (     ''     )
 *  - t[k] <= t[2k+2]             (if 2k+2 <= n)
 *  - t[2k+2..n] is itself a heap (     ''     )
 *
 * It is expressed by the predicate (heap t n k), defined as follows:
 *)

Inductive heap [N:Z; t:(array N Z); n:Z] : Z -> Prop :=
  heap_cons : (k:Z) 
     `0 <= k <= n`
  -> (`2*k+1 <= n` -> (Zge #t[k] #t[`2*k+1`]))
  -> (`2*k+1 <= n` -> (heap t n `2*k+1`))
  -> (`2*k+2 <= n` -> (Zge #t[k] #t[`2*k+2`]))
  -> (`2*k+2 <= n` -> (heap t n `2*k+2`))
  -> (heap t n k).

(* Some lemmas about heaps *)

(* A tree reduce to one element is a heap *)

Lemma heap_leaf :
  (N:Z)(t:(array N Z))(n:Z)(k:Z) 
    `0 <= k <= n` -> `2*k >= n` -> (heap t n k).
Proof.
Intros N t n k H1k H2k.
Apply heap_cons;
  [ Omega'
  | (Intro; Absurd `2*k >= n`; [ Omega' | Assumption ])
  | (Intro; Absurd `2*k >= n`; [ Omega' | Assumption ])
  | (Intro; Absurd `2*k >= n`; [ Omega' | Assumption ])
  | (Intro; Absurd `2*k >= n`; [ Omega' | Assumption ]) ].
Save.

(* The tree with only two elements (it is the case when 2k+1 is equal
 * to n, the greatest element) is a heap as soon as t[k] <= t[2k+1] *)

Lemma heap_son : 
  (N:Z)(t:(array N Z))(n:Z) `n >= 0` ->
    (k:Z) `2*k+1 = n` -> (Zge #t[k] #t[`2*k+1`]) -> (heap t n k).
Proof.
Intros N t n Hn k Hk Ht.
Apply heap_cons; 
  [ Omega'
  | Intro; Assumption
  | Intro; Apply heap_leaf; Omega'
  | Intro; Absurd `2*k+1 = n`; Omega' 
  | Intro; Absurd `2*k+1 = n`; Omega' ].
Save.

(* If we have a heap t[k..n] and t[k..n]=t'[k..n] then we have a heap
 * in t'[k..n] *)

Lemma heap_id :
  (N:Z)(t,t':(array N Z))(n,k:Z)
    (heap t n k) -> (array_id t t' k n) -> (heap t' n k).
Proof.
Intros N t t' n k H_heap.
Unfold array_id.
Elim H_heap; Intros; Clear H_heap.
Apply heap_cons. 
Assumption.
Intro; Rewrite <- (H6 k0); 
  [ Rewrite <- (H6 `2*k0+1`); [ Auto | Idtac ] | Idtac ]; 
  Clear H0 H1 H2 H3 H4 H5 H6; Omega'.
Intro; Apply H2; 
  [ Assumption 
  | Intros i Hi; Apply (H6 i); Clear H0 H1 H2 H3 H4 H5 H6; Omega' ].
Intro; Rewrite <- (H6 k0); 
  [ Rewrite <- (H6 `2*k0+2`); [ Auto | Idtac ] | Idtac ];
  Clear H0 H1 H2 H3 H4 H5 H6; Omega'.
Intro; Apply H5; 
  [ Assumption 
  | Intros i Hi; Apply (H6 i); Clear H0 H1 H2 H3 H4 H5 H6; Omega' ].
Save.

(* If t[k..n] is a heap then t[k..n-1] is a heap *)

Lemma heap_weakening :
  (N:Z)(t:(array N Z))(n,k:Z)
    `1 <= n` -> (heap t n k) -> `k <= n-1` -> (heap t `n-1` k).
Proof.
Intros N t n k Hn H. 
Elim H; Intros.
Apply heap_cons.
Clear H1 H2 H3 H4 H5 H6; Omega.
Intro; Apply H1; Clear H2 H3 H4 H5 H6; Omega.
Intro; Apply H3; Clear H1 H2 H4 H5 H6; Omega.
Intro; Apply H4; Clear H1 H2 H3 H5 H6; Omega.
Intro; Apply H6; Clear H1 H2 H3 H4 H5; Omega.
Save.

(* To prove the lemma heap_all (see further), we need an induction principle
 * following the structure of heaps *)

Lemma heap_induction :
  (P:Z->Prop)
  (P `0`) ->
  ((k:Z) `0 <= k` -> (P k) -> (P `2*k+1`) /\ (P `2*k+2`)) ->
  (k:Z)`0 <= k` -> (P k).
Proof.
Intros P H H0 k Hk; Generalize Hk; Pattern k; Apply Z_lt_induction.
Intros.
Elim (Z_modulo_2 x); [ Intro | Intro | Omega ].
(* x = 2y+2 *)
Elim (Z_le_lt_eq_dec `0` x). 
(* 0 < x *)
Intro.
(Elim a; Intros).
Replace x with `2*(x0-1)+2`.
Elim (H0 `x0-1`).
Auto. Omega.
Apply H1; Omega. Omega.
(* 0 = x *)
Intro H3. Rewrite <- H3. Assumption. Assumption.
(* x = 2y+1 *)
(Elim b; Intros).
Rewrite p.
Elim (H0 x0).
Auto. Omega.
(Apply H1; Omega).
Assumption.
Save.

(* If t[0..n] is a heap, then every sub-array t[k..n] is also a heap *)

Lemma heap_all :
  (N:Z)(t:(array N Z))(n:Z)
    (heap t n `0`) -> (i:Z)`0 <= i <= n` -> (heap t n i).
Proof.
Intros N t n H0 i H. Generalize H.
Pattern i.
Apply heap_induction. Auto.

Intros.
Split.
Intro. Generalize H3.
Elim H2. Intros.
(Apply H6; Intuition).

Omega.

Intro. Generalize H3. 
Elim H2. Intros.
(Apply H9; Intuition).

Omega.
Intuition.
Save.

