(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: WhyBool.v,v 1.4 2002-06-21 14:22:32 filliatr Exp $ *)

Require ZArith.
Require Sumbool.
Require Export Bool_nat.

Definition annot_bool :
  (b:bool) { b':bool | if b' then b=true else b=false }.
Proof.
Intro b.
Exists b. Case b; Trivial.
Save.


(* Logical connectives *)

Definition spec_and := [A,B,C,D:Prop][b:bool]if b then A /\ C else B \/ D.

Definition prog_bool_and :
  (Q1,Q2:bool->Prop) (sig bool Q1) -> (sig bool Q2)
  -> { b:bool | if b then (Q1 true) /\ (Q2 true)
                     else (Q1 false) \/ (Q2 false) }.
Proof.
Intros Q1 Q2 H1 H2.
Elim H1. Intro b1. Elim H2. Intro b2. 
Case b1; Case b2; Intros.
Exists true; Auto.
Exists false; Auto. Exists false; Auto. Exists false; Auto.
Save.

Definition spec_or := [A,B,C,D:Prop][b:bool]if b then A \/ C else B /\ D.

Definition prog_bool_or :
  (Q1,Q2:bool->Prop) (sig bool Q1) -> (sig bool Q2)
  -> { b:bool | if b then (Q1 true) \/ (Q2 true)
                     else (Q1 false) /\ (Q2 false) }.
Proof.
Intros Q1 Q2 H1 H2.
Elim H1. Intro b1. Elim H2. Intro b2. 
Case b1; Case b2; Intros.
Exists true; Auto. Exists true; Auto. Exists true; Auto.
Exists false; Auto.
Save.

Definition spec_not:= [A,B:Prop][b:bool]if b then B else A.

Definition prog_bool_not :
  (Q:bool->Prop) (sig bool Q)
  -> { b:bool | if b then (Q false) else (Q true) }.
Proof.
Intros Q H.
Elim H. Intro b.
Case b; Intro.
Exists false; Auto. Exists true; Auto.
Save.

(** Conversely, we build a [sumbool] out of a boolean, 
    for the need of validations *)

Definition btest
  [q:bool->Prop][b:bool][p:(q b)] : {(q true)}+{(q false)} :=
  (<[b:bool](q b)->{(q true)}+{(q false)}>
   Cases b of true => [p](left (q true) (q false) p) 
      | false => [p](right (q true) (q false) p) 
   end 
   p).
