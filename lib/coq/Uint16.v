(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.
Require int.Abs.
Require int.ComputerDivision.
Require Enum_intf.
Require Enum.

(* Why3 assumption *)
Definition in_bounds (n:Z): Prop := (0%Z <= n)%Z /\ (n <= 65535%Z)%Z.

Axiom t : Type.
Parameter t_WhyType : WhyType t.
Existing Instance t_WhyType.

Parameter to_int: t -> Z.

Axiom To_int_in_bounds : forall (a:t), (in_bounds (to_int a)).

Parameter of_int: Z -> t.

Axiom Of_int : forall (a:Z), (in_bounds a) -> ((to_int (of_int a)) = a).

(* Why3 assumption *)
Definition infix_pl (a:t) (b:t): t := (of_int ((to_int a) + (to_int b))%Z).

(* Why3 assumption *)
Definition prefix_mn (a:t): t := (of_int (-(to_int a))%Z).

(* Why3 assumption *)
Definition infix_mn (a:t) (b:t): t := (of_int ((to_int a) - (to_int b))%Z).

(* Why3 assumption *)
Definition infix_as (a:t) (b:t): t := (of_int ((to_int a) * (to_int b))%Z).

(* Why3 assumption *)
Definition infix_sl (a:t) (b:t): t :=
  (of_int (ZArith.BinInt.Z.quot (to_int a) (to_int b))).

(* Why3 assumption *)
Definition infix_pc (a:t) (b:t): t :=
  (of_int (ZArith.BinInt.Z.rem (to_int a) (to_int b))).

Axiom Extensionality1 : forall (x:t) (y:t), ((to_int x) = (to_int y)) ->
  (x = y).

Axiom Extensionality2 : forall (x:Z) (y:Z), ((of_int x) = (of_int y)) ->
  (((in_bounds x) /\ (in_bounds y)) -> (x = y)).

(* Why3 assumption *)
Definition infix_lseq (a:t) (b:t): Prop := ((to_int a) <= (to_int b))%Z.

(* Why3 assumption *)
Definition infix_ls (a:t) (b:t): Prop := ((to_int a) < (to_int b))%Z.

(* Why3 assumption *)
Definition infix_gteq (a:t) (b:t): Prop := ((to_int b) <= (to_int a))%Z.

(* Why3 assumption *)
Definition infix_gt (a:t) (b:t): Prop := ((to_int b) < (to_int a))%Z.

