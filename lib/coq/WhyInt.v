(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: WhyInt.v,v 1.2 2002-06-07 08:51:16 filliatr Exp $ *)

Require Export ZArith.
Require Export ZArith_dec.
Require Export Zdiv.

Theorem Znotzero : (x:Z){`x<>0`}+{`x=0`}.
Proof.
Intro x. Elim (Z_eq_dec x `0`) ; Auto.
Save.
