(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: WhyInt.v,v 1.1 2002-03-21 09:49:17 filliatr Exp $ *)

Require Export ZArith.
Require Export ZArith_dec.

Theorem Znotzero : (x:Z){`x<>0`}+{`x=0`}.
Proof.
Intro x. Elim (Z_eq_dec x `0`) ; Auto.
Save.
