(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: WhyBool.v,v 1.6 2002-10-31 16:16:33 filliatr Exp $ *)

Require ZArith.
Require Sumbool.

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


(** Equality over booleans *)

Definition B_eq_dec : (x,y:bool){x=y}+{~x=y}.
Proof. Decide Equality. Qed.

Definition B_eq_bool := 
 [x,y:bool](bool_of_sumbool (B_eq_dec x y)).

Definition B_noteq_bool := 
 [x,y:bool](bool_of_sumbool (sumbool_not ? ? (B_eq_dec x y))).

(** Equality over type unit *)

Definition U_eq_dec : (x,y:unit){x=y}+{~x=y}.
Proof. Decide Equality. Qed.

Definition U_eq_bool := 
 [x,y:unit](bool_of_sumbool (U_eq_dec x y)).

Definition U_noteq_bool := 
 [x,y:unit](bool_of_sumbool (sumbool_not ? ? (U_eq_dec x y))).

