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
Require Int8.
Require Uint64.
Require Bit_int8.
Require Bit_uint64.

Parameter cast_modulo: Int8.t -> Uint64.t.

Axiom Cast_modulo : forall (a:Int8.t),
  ((cast_modulo a) = (Uint64.of_int (Bit_uint64.normalize (Int8.to_int a)))).

