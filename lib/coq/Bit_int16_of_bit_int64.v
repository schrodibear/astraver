(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.
Require int.Abs.
Require int.EuclideanDivision.
Require int.ComputerDivision.
Require Enum_intf.
Require Enum.
Require Powers_of_2.
Require Bit_enum_intf.
Require Bit_enum.
Require Int16.
Require Int64.
Require Bit_int16.
Require Bit_int64.

Parameter cast_modulo: Int64.t -> Int16.t.

Axiom Cast_modulo : forall (a:Int64.t),
  ((cast_modulo a) = (Int16.of_int (Bit_int16.normalize (Int64.to_int a)))).

