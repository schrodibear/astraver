(**************************************************************************)
(*                                                                        *)
(* Proof of the Knuth-Morris-Pratt Algorithm.                             *)
(*                                                                        *)
(* Jean-Christophe Filliâtre (LRI, Université Paris Sud)                  *)
(* November 1998                                                          *)
(*                                                                        *)
(**************************************************************************)

(* The terminations of both initnext and kmp involve a lexicographic
 * order relation. *)

Require Export Relation_Operators.
Require Lexicographic_Product.

Implicit Arguments On.

Section lexico.

Variable A,B : Set.

Variable Ra : A->A->Prop.
Variable Rb : B->B->Prop.

Definition lex := (lexprod A [_:A]B Ra [_:A]Rb).

Lemma lex_well_founded :
  (well_founded A Ra) -> (well_founded B Rb) ->
  (well_founded {_:A & B} lex).
Proof.
Intros wfa wfb.
Exact (wf_lexprod A [_:A]B Ra [_:A]Rb wfa [_]wfb).
Save.

End lexico.

(* Instantiation on Z x Z *)

Require ZArith.
Require Zwf.

Definition prodZZ := {_:Z & Z}.

Definition pairZ : Z -> Z -> prodZZ := [x,y:Z](existS Z [_:Z]Z x y).

Definition lexZ := (lex (Zwf `0`) (Zwf `0`)).

Definition lexZ_well_founded :=
  (lex_well_founded (Zwf_well_founded `0`) (Zwf_well_founded `0`)).
