(**********************************************************************)
(*                                                                    *)
(* FIND, an historical example.                                       *)
(*                                                                    *)
(* The proof of this program was originally done by C. A. R. Hoare    *)
(* and fully detailed in the following paper:                         *)
(*                                                                    *)
(* C. A. R. Hoare, "Proof of a Program: FIND", Communications of the  *)
(* ACM, 14(1), 39--45, January 1971.                                  *)
(*                                                                    *)
(**********************************************************************)
(* Jean-Christophe FILLIATRE, February 98                             *)
(**********************************************************************)
(* find_proofs.v                                                      *)
(**********************************************************************)

Require find_spec.
Require find_lemmas.
Require Why.
Require Omega.

Lemma zero_f_SN : `0 <= f < (Zs N)`.
Proof.
Generalize le_1_f; Generalize le_f_N; Intros; Omega.
Save.

(* Lemmas to prove arrays bounds obligations. *)

Lemma bound_3 : (m,n,i,r:Z)(A:(array (Zs N) Z))
  (i_invariant m n i r A) ->
  `i <= n` ->
  (Zlt #A[i] r) ->
  `(Zs i) <= n`.
Proof.
Unfold i_invariant.
Intros m n i r A Hi le_i_n lt_Ai_r.
Decompose [and] Hi.
Case (Z_le_lt_eq_dec i n le_i_n).
Intro. Abstract Omega.
Intro eq_i_n. Elim (H2 le_i_n). Intros.
Absurd (Zlt #A[i] r).
Cut x=i. Intro eq_x_i. Rewrite eq_x_i in H0. Abstract Omega.
Abstract Omega.
Assumption.
Save.


Lemma bound_4 : (m,n,j,r:Z)(A:(array (Zs N) Z))
  (j_invariant m n j r A) ->
  `m <= j` ->
  (Zlt r #A[j]) ->
  `m <= (Zpred j)`.
Proof.
Unfold j_invariant.
Intros m n j r A Hj le_m_j lt_r_Aj.
Decompose [and] Hj.
Case (Z_le_lt_eq_dec m j le_m_j).
Intro. Unfold Zpred. Abstract Omega.
Intro eq_m_j. Elim (H2 le_m_j). Intros.
Absurd (Zlt r #A[j]).
Cut x=j. Intro eq_x_j. Rewrite eq_x_j in H0. Abstract Omega.
Abstract Omega.
Assumption.
Save.


(* Some subgoals of the main proof *)

Lemma subgoal_1 : (m1,n1,i2,j2,i3:Z)(A,A0,A1:(array (Zs N) Z))
  (m_invariant m1 A0)
          /\(n_invariant n1 A0)/\(permut A0 A)/\`1 <= m1`/\`n1 <= N` ->
  `m1 < n1` ->
  `0 <= f < (Zs N)` ->
  (i_invariant m1 n1 i2 (#A0[f]) A1)
    /\ (j_invariant m1 n1 j2 (#A0[f]) A1)
    /\ (m_invariant m1 A1)/\(n_invariant n1 A1)
    /\ `0 <= j2`/\`i2 <= N+1`
    /\(termination i2 j2 m1 n1 (#A0[f]) A1)
    /\(permut A1 A) ->
  `i2 <= j2` ->
  (i_invariant m1 n1 i3 (#A0[f]) A1)
    /\`i2 <= i3`
    /\`i3 <= n1` 
    /\(termination i3 j2 m1 n1 (#A0[f]) A1)->
  `(access   A1 i3) < (access   A0 f)` ->

  (i_invariant m1 n1 (Zs i3) (#A0[f]) A1)
   /\ `i2 <= (Zs i3)`
   /\ `(Zs i3) <= n1`
   /\ (termination (Zs i3) j2 m1 n1 (#A0[f]) A1).

Proof.
Intros m1 n1 i2 j2 i3 A A0 A1 HH_43 HH_42 HH_40 HH_28 HH_27 HH_4 HH_2.
Split.
Apply Lemma_8_15. Elim HH_4; Auto.
Decompose [and] HH_4. Elim H. Intros. Abstract Omega.
Split; [ Abstract Omega | Split ].
Cut `(Zs i3) <= n1`. Abstract Omega.
Apply bound_3 with m:=m1 r:=#A0[f] A:=A1; Auto.
Elim HH_4; Auto. Abstract Omega.
(* term. *)
Unfold termination. 
Decompose [and] HH_4. Elim H3.
Intro. Left. Abstract Omega.
Intro. Right. Decompose [and] H2.
Case (Z_le_lt_eq_dec i3 f H6).
  Intro. Abstract Omega.
  Intro eq_i3_f. Absurd `(access   A1 i3) < (access   A0 f)`; Auto.
  Rewrite eq_i3_f. Abstract Omega.
Save.


Lemma subgoal_2 : (m1,n1,i2,j2,i3,j3:Z)(A,A0,A1:(array (Zs N) Z))
  (m_invariant m1 A0)
    /\(n_invariant n1 A0)
    /\(permut A0 A)
    /\`1 <= m1`/\`n1 <= N` ->
  `m1 < n1` ->
  `0 <= f < (Zs N)` ->
  (i_invariant m1 n1 i2 (#A0[f]) A1)
    /\(j_invariant m1 n1 j2 (#A0[f]) A1)
    /\(m_invariant m1 A1)/\(n_invariant n1 A1)
    /\`0 <= j2`/\`i2 <= N+1`
    /\(termination i2 j2 m1 n1 (#A0[f]) A1)
    /\(permut A1 A) ->
  `i2 <= j2` ->
  ((i_invariant m1 n1 i3 (#A0[f]) A1)
     /\`i2 <= i3`/\`i3 <= n1`
     /\(termination i3 j2 m1 n1 (#A0[f]) A1))
    /\`(access   A1 i3) >= (access   A0 f)` ->
  (j_invariant m1 n1 j3 (#A0[f]) A1)
    /\`j3 <= j2`/\`m1 <= j3` 
    /\ (termination i3 j3 m1 n1 (#A0[f]) A1) ->
  `(access   A0 f) < (access   A1 j3)` ->

  (j_invariant m1 n1 (Zpred j3) (#A0[f]) A1)
    /\`(Zpred j3) <= j2`/\`m1 <= (Zpred j3)`
    /\(termination i3 (Zpred j3) m1 n1 (#A0[f]) A1).

Proof.
Intros m1 n1 i2 j2 i3 j3 A A0 A1 HH_43 HH_42 HH_40 HH_28 HH_27 
  HH_25 HH_9 HH_7.
Split.
Apply Lemma_9_17. Elim HH_9; Auto.
Unfold j_invariant in HH_9. Decompose [and] HH_9. Elim H3. Intros. Abstract Omega.
Assumption.
Cut `m1 <= (Zpred j3)`. Unfold Zpred. 
 Split ; [ Abstract Omega | Split ; [ Abstract Omega | Idtac ] ].
(* term. *)
Unfold termination.
Decompose [and] HH_9. Elim H4.
Intro. Left. Abstract Omega.
Intro. Right. Decompose [and] H3.
Case (Z_le_lt_eq_dec f j3 H8).
  Intro. Abstract Omega.
  Intro eq_f_j3. Absurd `(access   A0 f) < (access   A1 j3)`; Auto.
  Rewrite <- eq_f_j3. Abstract Omega.
(* *)
Apply bound_4 with n:=n1 r:=#A0[f] A:=A1; Auto.
Elim HH_9; Auto. Abstract Omega.
Save.


Lemma subgoal_3 : (m0,n0,i0,j0,i1,j1:Z)(A,A0,A1,A2:(array (Zs N) Z))
  (m_invariant m0 A0)
           /\(n_invariant n0 A0)/\(permut A0 A)/\`1 <= m0`/\`n0 <= N`
 -> `m0 < n0`
 -> `0 <= f < (Zs N)`
 -> (i_invariant m0 n0 i0 (#A0[f]) A1)
           /\(j_invariant m0 n0 j0 (#A0[f]) A1)
             /\(m_invariant m0 A1)
               /\(n_invariant n0 A1)
                 /\`0 <= j0`
                   /\`i0 <= N+1`
                     /\(termination i0 j0 m0 n0 (#A0[f]) A1)
                       /\(permut A1 A)
 -> `i0 <= j0`
 -> ((i_invariant m0 n0 i1 (#A0[f]) A1)
           /\`i0 <= i1`
             /\`i1 <= n0`/\(termination i1 j0 m0 n0 (#A0[f]) A1))
          /\`(access   A1 i1) >= (access   A0 f)`
 -> ((j_invariant m0 n0 j1 (#A0[f]) A1)
           /\`j1 <= j0`
             /\`m0 <= j1`/\(termination i1 j1 m0 n0 (#A0[f]) A1))
          /\`(access   A0 f) >= (access   A1 j1)`
 -> `(access   A1 j1) <= (access   A0 f) <= (access   A1 i1)`
 -> `i1 <= j1`
 -> (exchange A2 A1 i1 j1)
 -> `(access   A2 i1) <= (access   A0 f)`
 -> `(access   A0 f) <= (access   A2 j1)`
 -> (Zwf `0` `N+2+(Zpred j1)-(Zs i1)` `N+2+j0-i0`)
   /\(i_invariant m0 n0 (Zs i1) (#A0[f]) A2)
     /\(j_invariant m0 n0 (Zpred j1) (#A0[f]) A2)
       /\(m_invariant m0 A2)
         /\(n_invariant n0 A2)
           /\`0 <= (Zpred j1)`
             /\`(Zs i1) <= N+1`
               /\(termination (Zs i1) (Zpred j1) m0 n0 (#A0[f]) A2)
                 /\(permut A2 A).
Proof.
Intros m0 n0 i0 j0 i1 j1 A A0 A1 A2 Inv_mn Test7 Pre12 Inv_ij Test4 Inv_i 
  Inv_j Pre10 Test3 Post7 Pre8 Pre7.
Split.
(* [Zwf] *)
  Unfold Zwf.
  Decompose [and] Inv_i. Decompose [and] Inv_j. Unfold Zpred. 
  Abstract Omega.
Split.
(* [i_invariant] *)
  Apply Lemma_8_10 with j:=j1 A':=A1 ; Try Assumption.
  Decompose [and] Inv_i. Elim H1. Abstract Omega.
  Abstract Omega. Abstract Omega.  
  Decompose [and] Inv_i. Assumption.
  Decompose [and] Inv_j. Assumption.
Split.
(* [j_invariant] *)
  Apply Lemma_9_11 with i:=i1 A':=A1 ; Try Assumption.
  Decompose [and] Inv_j. Elim H1. Abstract Omega. 
  Decompose [and] Inv_i. Elim H1. Abstract Omega. 
  Decompose [and] Inv_mn. Assumption.
  Decompose [and] Inv_j. Assumption.
  Decompose [and] Inv_i. Assumption.
Split.
(* [m_invariant] *)
  Apply Lemma_12' with i:=i1 j:=j1 A:=A1.
  Decompose [and] Inv_i. Elim H1. Abstract Omega.
  Auto with datatypes.
  Decompose [and] Inv_ij. Assumption.
Split.
(* [n_invariant] *)
  Apply Lemma_13' with i:=i1 j:=j1 A:=A1.
  Decompose [and] Inv_i. Elim H1. Abstract Omega.
  Decompose [and] Inv_j. Elim H1. Abstract Omega.
  Auto with datatypes.
  Decompose [and] Inv_ij. Assumption.
Split.
(* [0<=j-1] *)
  Unfold Zpred. Abstract Omega.
Split.
(* [i+1<=N+1] *)
  Abstract Omega.
Split.
(* [termination] *)
  Unfold termination. 
  Left. Unfold Zpred. 
  Decompose [and] Inv_i. Elim H1. Intros. 
  Decompose [and] Inv_j. Elim H8. Intros. 
  Abstract Omega.
(* [permut] *)
  Decompose [and] Inv_ij. EAuto with datatypes.
Save.


Lemma subgoal_5 : (m1,n1,i2,j2:Z)(A,A0,A1:(array (Zs N) Z))
  (m_invariant m1 A0)
    /\(n_invariant n1 A0)
    /\(permut A0 A)
    /\`1 <= m1`/\`n1 <= N` ->
  `m1 < n1` ->
  `0 <= f < (Zs N)` ->
  ((i_invariant m1 n1 i2 (#A0[f]) A1)
     /\(j_invariant m1 n1 j2 (#A0[f]) A1)
     /\(m_invariant m1 A1)/\(n_invariant n1 A1)
     /\`0 <= j2`/\`i2 <= N+1`
     /\(termination i2 j2 m1 n1 (#A0[f]) A1)
     /\(permut A1 A))
    /\`i2 > j2` ->
  `m1 < i2`/\`j2 < n1` ->
  `f <= j2` ->

  (Zwf `0` `j2-m1` `n1-m1`)
   /\(m_invariant m1 A1)
     /\(n_invariant j2 A1)/\(permut A1 A)/\`1 <= m1`/\`j2 <= N`.

Proof.
Intros m1 n1 i2 j2 A A0 A1 HH_44 HH_43 HH_41 HH_40 HH_39 HH_37.
Decompose [and] HH_40.
Split; [ Idtac | Split; [ Assumption | Split ; 
           [ Idtac | Split ; [ Assumption | Idtac ]]]].
Abstract (Unfold Zwf; Elim H; Elim H0; Elim H1; Elim H2; Intros; Omega).
Apply Lemma_6_a with m:=m1 n:=n1 i:=i2 r:=#A0[f]; Auto.
Abstract Omega.
Save.


Lemma subgoal_6 : (m1,n1,i2,j2:Z)(A,A0,A1:(array (Zs N) Z))
  (m_invariant m1 A0)
    /\(n_invariant n1 A0)
    /\(permut A0 A)
    /\`1 <= m1`/\`n1 <= N` ->
  `m1 < n1` ->
  `0 <= f < (Zs N)` ->
  ((i_invariant m1 n1 i2 (#A0[f]) A1)
     /\(j_invariant m1 n1 j2 (#A0[f]) A1)
     /\(m_invariant m1 A1)/\(n_invariant n1 A1)
     /\`0 <= j2`/\`i2 <= N+1`
     /\(termination i2 j2 m1 n1 (#A0[f]) A1)
     /\(permut A1 A))
    /\`i2 > j2` ->
  `m1 < i2`/\`j2 < n1` ->
  `f > j2` ->
  `i2 <= f` -> 

  (Zwf `0` `n1-i2` `n1-m1`)
   /\(m_invariant i2 A1)
     /\(n_invariant n1 A1)/\(permut A1 A)/\`1 <= i2`/\`n1 <= N`.
Proof.
Intros m1 n1 i2 j2 A A0 A1 HH_44 HH_43 HH_41 HH_40 HH_39 HH_36 HH_33.
Decompose [and] HH_40.
Split; [ Idtac | Split ; [Idtac | Split ; [ Assumption | Split ; 
          [ Assumption | Idtac ]]]].
Abstract (Unfold Zwf; Elim H; Elim H1; Elim H2; Elim H3; Intros; Omega).
Apply Lemma_6_b with m:=m1 n:=n1 j:=j2 r:=#A0[f]; Auto.
Abstract Omega.
Save.


Lemma subgoal_7 : (m1,n1,i2,j2:Z)(A,A0,A1:(array (Zs N) Z))
  (m_invariant m1 A0)
    /\(n_invariant n1 A0)/\(permut A0 A)/\`1 <= m1`/\`n1 <= N` ->
  `m1 < n1` ->
  `0 <= f < (Zs N)` ->
  ((i_invariant m1 n1 i2 (#A0[f]) A1)
     /\(j_invariant m1 n1 j2 (#A0[f]) A1)
     /\(m_invariant m1 A1)/\(n_invariant n1 A1)
     /\`0 <= j2`/\`i2 <= N+1`
     /\(termination i2 j2 m1 n1 (#A0[f]) A1)
     /\(permut A1 A))
     /\`i2 > j2` ->
  `m1 < i2`/\`j2 < n1` ->
  `f > j2` ->
  `i2 > f` -> 

  (Zwf `0` `f-f` `n1-m1`)
   /\(m_invariant f A1)
     /\(n_invariant f A1)/\(permut A1 A)/\`1 <= f <= N`.

Proof.
Intros m1 n1 i2 j2 A A0 A1 HH_44 HH_43 HH_41 HH_40 HH_39 HH_36 HH_32.
Decompose [and] HH_40.
Split; [ Idtac | Split ; [ Idtac | Split ; [ Idtac | Split ; 
           [ Assumption | Idtac ]]]].
Abstract (Unfold Zwf; Elim H; Elim H0; Elim H1; Elim H2; Intros; Omega).
Apply Lemma_6_c1 with m :=m1 n:=n1 i:=i2 j:=j2 r:=#A0[f]; Auto.
Abstract Omega.
Apply Lemma_6_c2 with m :=m1 n:=n1 i:=i2 j:=j2 r:=#A0[f]; Auto.
Abstract Omega.
Abstract Omega.
Save.
