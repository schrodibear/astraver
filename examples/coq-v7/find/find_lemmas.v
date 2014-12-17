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
(* find_lemmas.v                                                      *)
(**********************************************************************)

Require find_spec.
Require Why.
Require Omega.

(* Lemmas *)

Lemma Lemma_1 : (A:(array Z))
  (m_invariant `1` A).
Proof.
Intro A. Unfold m_invariant.
Split ; [ Exact le_1_f | Intros ].
Absurd `1 <= p`; Abstract Omega.
Save.

Lemma Lemma_2 : (A:(array Z))
  (n_invariant N A).
Proof.
Intro A. Unfold n_invariant.
Split ; [ Exact le_f_N | Intros ].
Absurd `q <= N`; Abstract Omega.
Save.

Lemma Lemma_3 : (m,n:Z)(A:(array Z))
    (m_invariant m A)
 -> (n_invariant n A)
 -> `m >= n`
 -> (found A).
Proof.
Unfold m_invariant n_invariant found.
Intros m n A H_m H_n le_n_m p q H1 H2 H3 H4.
Cut m=f. Cut n=f. Intros eq_m_f eq_n_f.
Decompose [and] H_m. Decompose [and] H_n.
Split.
Case (Z_le_lt_eq_dec p f H2).
  Intro lt_p_f. Generalize (H0 p f). Intros. Abstract Omega.
  Intro eq_p_f. Rewrite eq_p_f. Abstract Omega.
Case (Z_le_lt_eq_dec f q H3).
  Intro lt_f_q. Generalize (H6 f q). Intros. Abstract Omega.
  Intro eq_f_q. Rewrite eq_f_q. Abstract Omega.
Abstract Omega.
Abstract Omega.
Save.

Lemma Lemma_4 : (m:Z)(A:(array Z))
    (m_invariant m A)
 -> (p:Z) `1 <= p < m` -> (Zle #A[p] #A[f]).
Proof.
Unfold m_invariant. Intros m A H_m p H_p.
Decompose [and] H_m.
Generalize (H0 p f).
Intros. Generalize le_f_N. Abstract Omega.
Save.

Lemma Lemma_5 : (n:Z)(A:(array Z))
    (n_invariant n A)
 -> (q:Z) `n < q <= N` -> (Zle #A[f] #A[q]).
Proof.
Unfold n_invariant. Intros n A H_n q H_q.
Decompose [and] H_n.
Generalize (H0 f q).
Intros. Generalize le_1_f. Abstract Omega.
Save.

Lemma Lemma_6_a : (m,n,i,j,r:Z)(A:(array Z))
    `i > j`
 -> (m_invariant m A) -> (n_invariant n A)
 -> (i_invariant m n i r A) -> (j_invariant m n j r A)
 -> `f <= j`
 -> (n_invariant j A).
Proof.
Unfold m_invariant n_invariant i_invariant j_invariant.
Intros m n i j r A lt_i_j H_m H_n H_i H_j le_f_j.
Decompose [and] H_m. Decompose [and] H_n. 
Decompose [and] H_i. Decompose [and] H_j. 
Clear H_m H_n H_i H_j.
Split.
Assumption.
Intros. 
Generalize (H5 p). Generalize (H8 q).
Abstract Omega.
Save.

Lemma Lemma_6_b : (m,n,i,j,r:Z)(A:(array Z))
    `i > j`
 -> (m_invariant m A) -> (n_invariant n A)
 -> (i_invariant m n i r A) -> (j_invariant m n j r A)
 -> `i <= f`
 -> (m_invariant i A).
Proof.
Unfold m_invariant n_invariant i_invariant j_invariant.
Intros m n i j r A lt_j_i H_m H_n H_i H_j le_i_f.
Decompose [and] H_m. Decompose [and] H_n. 
Decompose [and] H_i. Decompose [and] H_j. 
Clear H_m H_n H_i H_j.
Split.
Assumption.
Intros. 
Generalize (H5 p). Generalize (H8 q).
Abstract Omega.
Save.

Lemma Lemma_6_c1 : (m,n,i,j,r:Z)(A:(array Z))
    `i > j`
 -> (m_invariant m A) -> (n_invariant n A)
 -> (i_invariant m n i r A) -> (j_invariant m n j r A)
 -> `j < f < i`
 -> (m_invariant f A).
Proof.
Unfold m_invariant n_invariant i_invariant j_invariant.
Intros m n i j r A lt_j_i H_m H_n H_i H_j lt_j_f_i.
Decompose [and] H_m. Decompose [and] H_n. 
Decompose [and] H_i. Decompose [and] H_j. 
Clear H_m H_n H_i H_j.
Split.
Abstract Omega.
Intros.
Generalize (H5 p). Generalize (H8 q).
Abstract Omega.
Save.

Lemma Lemma_6_c2 : (m,n,i,j,r:Z)(A:(array Z))
    `i > j`
 -> (m_invariant m A) -> (n_invariant n A)
 -> (i_invariant m n i r A) -> (j_invariant m n j r A)
 -> `j < f < i`
 -> (n_invariant f A).
Proof.
Unfold m_invariant n_invariant i_invariant j_invariant.
Intros m n i j r A lt_j_i H_m H_n H_i H_j lt_j_f_i.
Decompose [and] H_m. Decompose [and] H_n. 
Decompose [and] H_i. Decompose [and] H_j. 
Clear H_m H_n H_i H_j.
Split.
Abstract Omega.
Intros.
Generalize (H5 p). Generalize (H8 q).
Abstract Omega.
Save.

(* Lemma 7 is not useful because we don't do a \verb"goto L" statement
   to exit the loop. Actually, we do \verb"n := f; m := f" and [Lemma_6_c1]
   and [Lemma_6_c2] are what we need *)

Lemma Lemma_8 : (i,m,r:Z)(A:(array Z))
    (Zle #A[i] r)
 -> ((Zle m i) /\ ((p:Z)((Zle `1` p)->(Zlt p i)->(Zle #A[p] r))))
 -> ((Zle m (Zs i)) /\ ((p:Z)((Zle `1` p)->(Zlt p (Zs i))->(Zle #A[p] r)))).
Proof.
Intros i m r A H H0.
Decompose [and] H0.
Split.
Abstract Omega.
Intros.
Elim (Z_le_lt_eq_dec p i); [ Auto | Idtac | Abstract Omega ].
Intro Heq. Rewrite Heq. Auto.
Save.

Lemma Lemma_9 : (j,n,r:Z)(A:(array Z))
    (Zle r #A[j])
 -> ((Zle j n) /\ ((q:Z)((Zlt j q)->(Zle q N)->(Zle r #A[q]))))
 -> (  (Zle (Zpred j) n) 
    /\ ((q:Z)((Zlt (Zpred j) q)->(Zle q N)->(Zle r #A[q])))).
Proof.
Intros j n r A H H0.
Decompose [and] H0.
Split.
Unfold Zpred. Abstract Omega.
Intros.
Elim (Z_le_lt_eq_dec j q).
Auto.
Intro Heq. Rewrite <- Heq. Auto.
Unfold Zpred in H3. Abstract Omega.
Save.

Lemma Lemma_10 : (m,i,j,r:Z)(A,A':(array Z))
    `m <= i <= j`
 -> (exchange A A' i j)
 -> ((p:Z)(`1<=p` -> `p<i` -> (Zle #A[p] r)))
 -> `m <= i` /\ ((p:Z)(`1<=p` -> `p<i` -> (Zle #A'[p] r))).
Proof.
Intros m i j r A A' H_i_j H_ex H_A.
Elim H_ex. Intros H_l H_i H_j H_Ai H_Aj H_Ak.
Split; [ Abstract Omega | Intros p H1 H2 ].
Generalize (H_Ak p). Intros.
Generalize (H_A p). Intros. Abstract Omega.
Save.

Lemma Lemma_8_10_1 : (m,n,i,j,r:Z)(A,A':(array Z))
  `m <= i <= j` ->
  `n <= N` ->
  `1 <= m` ->
  (exchange A A' i j) ->
  (Zle #A[i] r) ->
  (Zle r #A[j]) ->
  (i_invariant m n i r A') -> 
  (j_invariant m n j r A') -> 
  (i_invariant m n i r A).
Proof.
Intros m n i j r A A' H_i_j le_n_N le_1_m H_ex H_i_r H_r_j H_i H_j.
Unfold i_invariant. Unfold i_invariant in H_i. Decompose [and] H_i.
Split; [ Abstract Omega | Split ].
Intros p H1' H2'. 
Cut (exchange A' A i j). Intro H_ex'.
Elim (Lemma_10 m i j r A' A H_i_j H_ex' H1).
Auto. Auto with datatypes.
Intro. Exists j. 
  Unfold j_invariant in H_j. Decompose [and] H_j.
  Abstract Omega.
Save.

Lemma Lemma_8_10 : (m,n,i,j,r:Z)(A,A':(array Z))
  `(array_length A)=N+1` -> 
  `m <= i <= j` ->
  `n <= N` ->
  `1 <= m` ->
  (exchange A A' i j) ->
  (Zle #A[i] r) ->
  (Zle r #A[j]) ->
  (i_invariant m n i r A') -> 
  (j_invariant m n j r A') -> 
  (i_invariant m n (Zs i) r A).
Proof.
Intros m n i j r A A' Hl H_i_j le_n_N le_1_m H_ex H_i_r H_r_j H_i H_j.
Cut (i_invariant m n i r A). Intro H_int. 
Unfold i_invariant. 
Unfold i_invariant in H_int. Decompose [and] H_int.
Split; [ Abstract Omega | Split ].
Intros p H1' H2'. 
Elim (Lemma_8 i m r A H_i_r (conj ? ? H H1)); Auto.
Unfold j_invariant in H_j. Decompose [and] H_j.
Cut `i<=j`. Intro le_i_j. Case (Z_le_lt_eq_dec i j le_i_j). 
  Intros. Exists j. Abstract Omega.
Intros eq_i_j lt_i_n.
  Exists (Zs i).
  Split ; [ Abstract Omega | Split; [ Assumption | Idtac ] ].
  Generalize (exchange_id H_ex eq_i_j). Intro Hk.
  Cut (access A (Zs i))=(access A' (Zs i)). Intro Hr. Rewrite Hr.
  Apply (H4 (Zs i)); Abstract Omega.
  Apply (Hk (Zs i)); Try Omega.
Omega.
Apply Lemma_8_10_1 with j:=j A':=A'; Assumption.
Save.

Lemma Lemma_11 : (n,i,j,r:Z)(A,A':(array Z))
 `(array_length A)=N+1`
 -> `i <= j <= n`
 -> (exchange A A' i j)
 -> ((q:Z)(`j<q` -> `q<=N` -> (Zle r #A[q])))
 -> `j <= n` /\ ((q:Z)(`j<q` -> `q<=N` -> (Zle r #A'[q]))).
Proof.
Intros n i j r A A' HN H_i_j H_ex H_A.
Elim H_ex. Intros Hl H_i H_j H_Ai H_Aj H_Ak.
Split; [ Abstract Omega | Intros q H1 H2 ].
Generalize (H_Ak q). Intros.
Generalize (H_A q). Intros. Abstract Omega.
Save.

Lemma Lemma_9_11_1 : (m,n,i,j,r:Z)(A,A':(array Z))
  `(array_length A)=N+1` -> 
  `i <= j <= n` ->
  `n <= N` ->
  `1 <= m` ->
  (exchange A A' i j) ->
  (Zle #A[i] r) ->
  (Zle r #A[j]) ->
  (j_invariant m n j r A') -> 
  (i_invariant m n i r A') -> 
  (j_invariant m n j r A).
Proof.
Intros m n i j r A A' HN H_i_j le_n_N le_1_m H_ex H_i_r H_r_j H_j H_i.
Unfold j_invariant. Unfold j_invariant in H_j. Decompose [and] H_j.
Split; [ Abstract Omega | Split ].
Intros q H1' H2'. 
Cut (exchange A' A i j). Intro H_ex'.
SameLength A A'. Rewrite H0 in HN.
Elim (Lemma_11 n i j r A' A HN H_i_j H_ex' H1).
Auto. Auto with datatypes.
Intro. Exists i. 
  Unfold i_invariant in H_i. Decompose [and] H_i.
  Abstract Omega.
Save.

Lemma Lemma_9_11 : (m,n,i,j,r:Z)(A,A':(array Z))
  `(array_length A)=N+1` -> 
  `i <= j <= n` ->
  `n <= N` ->
  `1 <= m` ->
  (exchange A A' i j) ->
  (Zle #A[i] r) ->
  (Zle r #A[j]) ->
  (j_invariant m n j r A') -> 
  (i_invariant m n i r A') -> 
  (j_invariant m n (Zpred j) r A).
Proof.
Intros m n i j r A A' HN H_i_j le_n_N le_1_m H_ex H_i_r H_r_j H_j H_i.
Cut (j_invariant m n j r A). Intro H_int. 
Unfold j_invariant. 
Unfold j_invariant in H_int. Decompose [and] H_int.
Split; [ Unfold Zpred; Abstract Omega | Split ].
Intros q H1' H2'. 
Elim (Lemma_9 j n r A H_r_j (conj ? ? H H1)); Auto.
Unfold i_invariant in H_i. Decompose [and] H_i.
Cut `i<=j`. Intro le_i_j. Case (Z_le_lt_eq_dec i j le_i_j). 
  Intros. Exists i. Unfold Zpred. Abstract Omega.
Intros eq_i_j lt_m_j.
  Exists (Zpred j). 
  Split ; [ Unfold Zpred; Unfold Zpred in lt_m_j; Abstract Omega 
          | Split; [ Unfold Zpred; Unfold Zpred in lt_m_j; Abstract Omega | Idtac ] ].
  Generalize (exchange_id H_ex eq_i_j). Intro Hk.
  Cut (access A (Zpred j))=(access A' (Zpred j)). Intro Hr. Rewrite Hr.
  Apply (H4 (Zpred j)); Unfold Zpred; Unfold Zpred in lt_m_j; Abstract Omega.
  Apply (Hk (Zpred j)); Unfold Zpred; Abstract Omega.
Abstract Omega.
Apply Lemma_9_11_1 with i:=i A':=A'; Assumption.
Save.

Lemma Lemma_12 : (m,i,j:Z)(A,A':(array Z))
    `(array_length A)=N+1`
 -> `m <= i <= j`
 -> (exchange A A' i j)
 -> ((p,q:Z)(`1<=p` -> `p<m` -> `m<=q` -> `q<=N` -> (Zle #A[p] #A[q])))
 -> ((p,q:Z)(`1<=p` -> `p<m` -> `m<=q` -> `q<=N` -> (Zle #A'[p] #A'[q]))).
Proof.
Intros m i j A A' HN H_m_i_j H_ex H_A p q H1 H2 H3 H4.
Elim H_ex. Intros Hl H_i H_j H_ij H_ji H_k.
Cut #A'[p]=#A[p]. Intro H_A'p_Ap.
Case (Z_eq_dec q i).
  Intro eq_q_i.
  Generalize (H_A p j H1 H2). Intro H6.
  Rewrite eq_q_i. Abstract Omega.
Intro not_eq_q_i. Case (Z_eq_dec q j).
  Intro eq_q_j.
  Generalize (H_A p i H1 H2). Intro H6.
  Rewrite eq_q_j. Abstract Omega.
Intro not_eq_q_j.
  Generalize (H_k q). Intros.
  Generalize (H_A p q). Intros.
  Abstract Omega.
Generalize (H_k p). Intros. Abstract Omega.
Save.

Lemma Lemma_12' : (m,i,j:Z)(A,A':(array Z))
    `(array_length A)=N+1`
 -> `m <= i <= j`
 -> (exchange A A' i j)
 -> (m_invariant m A)
 -> (m_invariant m A').
Proof.
Unfold m_invariant.
Intros m i j A A' HN H_m_i_j H_ex H_m.
Decompose [and] H_m.
Split; [ Assumption | Idtac ].
Exact (Lemma_12 m i j A A' HN H_m_i_j H_ex H0).
Save.

Lemma Lemma_13 : (n,i,j:Z)(A,A':(array Z))
    `(array_length A)=N+1`
 -> `1 <= i`
 -> `i <= j <= n`
 -> (exchange A A' i j)
 -> ((p,q:Z)(`1<=p` -> `p<=n` -> `n<q` -> `q<=N` -> (Zle #A[p] #A[q])))
 -> ((p,q:Z)(`1<=p` -> `p<=n` -> `n<q` -> `q<=N` -> (Zle #A'[p] #A'[q]))).
Proof.
Intros n i j A A' HN le_1_i H_n_i_j H_ex H_A p q H1 H2 H3 H4.
Elim H_ex. Intros Hl H_i H_j H_ij H_ji H_k.
Cut #A'[q]=#A[q]. Intro H_A'q_Aq.
Case (Z_eq_dec p i).
  Intro eq_p_i.
  Generalize (H_A j q). Intro H6.
  Rewrite eq_p_i. Abstract Omega.
Intro not_eq_p_i. Case (Z_eq_dec p j).
  Intro eq_p_j.
  Generalize (H_A i q). Intro H6.
  Rewrite eq_p_j. Abstract Omega.
Intro not_eq_p_j.
  Generalize (H_k p). Intros.
  Generalize (H_A p q). Intros.
  Abstract Omega.
Generalize (H_k q). Intros. Abstract Omega.
Save.

Lemma Lemma_13' : (n,i,j:Z)(A,A':(array Z))
    `(array_length A)=N+1`
 -> `1 <= i`
 -> `i <= j <= n`
 -> (exchange A A' i j)
 -> (n_invariant n A)
 -> (n_invariant n A').
Proof.
Unfold n_invariant.
Intros n i j A A' HN le_1_i H_i_j_n H_ex H_n.
Decompose [and] H_n.
Split; [ Assumption | Idtac ].
Exact (Lemma_13 n i j A A' HN le_1_i H_i_j_n H_ex H0).
Save.

Lemma Lemma_14 : (m,n:Z)(A:(array Z))
     `m <= f <= n`
  -> (EX p:Z | `m <= p` /\ `p <= n` /\ (Zle #A[f] #A[p])).
Proof.
Intros m n A H_m_f_n.
Exists f. Abstract Omega.
Save.

Lemma Lemma_4_14 : (m,n:Z)(A:(array Z))
    `m <= f <= n`
 -> (m_invariant m A)
 -> (i_invariant m n m #A[f] A).
Proof.
Intros m n A H_f H_m.
Unfold i_invariant.
Split ; [ Abstract Omega | Split ].
Intros. EApply Lemma_4 ; EAuto.
Intro. Apply Lemma_14; Auto.
Save.

Lemma Lemma_14' : (m,n:Z)(A:(array Z))
     `m <= f <= n`
  -> (EX q:Z | `m <= q` /\ `q <= n` /\ (Zle #A[q] #A[f])).
Proof.
Intros m n A H_m_f_n.
Exists f. Abstract Omega.
Save.

Lemma Lemma_5_14' : (m,n:Z)(A:(array Z))
    `m <= f <= n`
 -> (n_invariant n A)
 -> (j_invariant m n n #A[f] A).
Proof.
Intros m n A H_f H_n.
Unfold j_invariant.
Split ; [ Abstract Omega | Split ].
Intros. EApply Lemma_5 ; EAuto.
Intro. Apply Lemma_14'; Auto.
Save.

Lemma Lemma_15 : (n,i,r:Z)(A:(array Z))
    (Zlt #A[i] r)
 -> (EX p:Z | (Zle i p) /\ (Zle p n) /\ (Zle r #A[p]))
 -> (EX p:Z | (Zle (Zs i) p) /\ (Zle p n) /\ (Zle r #A[p])).
Proof.
Intros n i r A H H0.
Elim H0. Intros p Hp. Decompose [and] Hp.
Case (Z_le_lt_eq_dec i p H1).
Intro. Exists p. Abstract Omega.
Intro eq_i_p. Absurd (Zle r #A[p]). Rewrite <- eq_i_p. Abstract Omega. Assumption.
Save.

Lemma Lemma_8_15 : (i,m,n,r:Z)(A:(array Z))
    (i_invariant m n i r A)
 -> (Zlt #A[i] r)
 -> (i_invariant m n (Zs i) r A).
Proof.
Unfold i_invariant.
Intros i m n r A H H0.
Decompose [and] H.
Split.
Abstract Omega.
Split.
Elim (Lemma_8 i m r A) ; [ Auto | Abstract Omega | Auto ].
Intro. Apply Lemma_15; Auto. Apply H4; Abstract Omega.
Save.


Lemma Lemma_17' : (j,m,n,r:Z)(A:(array Z))
    (j_invariant m n j r A)
 -> (Zle `1` m)
 -> (Zle m j)
 -> (Zlt r #A[j])
 -> (Zlt `0` j).
Proof.
Unfold j_invariant.
Intros j m n r A H Hm le_m_j H0.
Decompose [and] H.
Elim (H4 le_m_j). Intros q Hq. Decompose [and] Hq.
  Case (Z_le_lt_eq_dec q j H6).
    Intro. Abstract Omega.
    Intro eq_q_j. Absurd (Zle #A[q] r). Rewrite eq_q_j. 
    Abstract Omega. Assumption.
Save.

Lemma Lemma_17 : (m,j,r:Z)(A:(array Z))
    (Zlt r #A[j])
 -> (EX q:Z | (Zle m q) /\ (Zle q j) /\ (Zle #A[q] r))
 -> (EX q:Z | (Zle m q) /\ (Zle q (Zpred j)) /\ (Zle #A[q] r)).
Proof.
Intros m j r A H H0.
Elim H0. Intros q Hq. Decompose [and] Hq.
Case (Z_le_lt_eq_dec q j H3).
Intro. Exists q. Unfold Zpred. Abstract Omega.
Intro eq_q_j. Absurd (Zle #A[q] r). Rewrite eq_q_j. Abstract Omega. Assumption.
Save.

Lemma Lemma_9_17 : (j,m,n,r:Z)(A:(array Z))
    (j_invariant m n j r A)
 -> (Zlt r #A[j])
 -> (j_invariant m n (Zpred j) r A).
Proof.
Unfold j_invariant.
Intros j m n r A H H0.
Decompose [and] H.
Split.
Unfold Zpred. Abstract Omega.
Split.
Elim (Lemma_9 j n r A) ; [ Auto | Abstract Omega | Auto ].
Intro. Apply Lemma_17; Auto. Apply H4.
Unfold Zpred in H2; Abstract Omega.
Save.
