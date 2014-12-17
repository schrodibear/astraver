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
(* find_spec.v                                                        *)
(**********************************************************************)

Require Export WhyArrays.

(* parameters = globals of the program *)

Parameter N : Z.   (* size of the array *)
Parameter f : Z.   (* the `pivot' *)

Axiom le_1_f : `1 <= f`.
Axiom le_f_N : `f <= N`.

(* Specification part *)

Definition n_invariant :=
  [n:Z][A:(array Z)]
     `f <=n`
  /\ (p,q:Z)(`1<=p` -> `p<=n` -> `n<q` -> `q<=N` -> (Zle #A[p] #A[q])).

Definition m_invariant :=
  [m:Z][A:(array Z)]
     (Zle m f)
  /\ (p,q:Z)(`1<=p` -> `p<m` -> `m<=q` -> `q<=N` -> (Zle #A[p] #A[q])).

Definition i_invariant :=
  [m,n,i,r:Z][A:(array Z)]
     (Zle m i)
  /\ ((p:Z)(`1<=p` -> `p<i` -> (Zle #A[p] r)))
  /\ (`i<=n` -> (EX p:Z | `i<=p` /\ `p<=n` /\ (Zle r #A[p]))).
  
Definition j_invariant :=
  [m,n,j,r:Z][A:(array Z)]
     (Zle j n)
  /\ ((q:Z)(`j<q` -> `q<=N` -> (Zle r #A[q])))
  /\ (`m<=j` -> (EX q:Z | `m<=q` /\ `q<=j` /\ (Zle #A[q] r))).

Definition termination :=
  [i,j,i0,j0,r:Z][A:(array Z)]
    (`i>i0` /\ `j<j0`) \/ (`i<=f<=j` /\ #A[f]=r).

Definition found :=
  [A:(array Z)]
    (p,q:Z)`1<=p` -> `p<=f` -> `f<=q` -> `q<=N` 
      	     -> (Zle #A[p] #A[f]) /\ (Zle #A[f] #A[q]).

