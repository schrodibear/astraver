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
Require Uint8.
Require Bit_int8.
Require Bit_uint8.

Parameter cast_modulo: Uint8.t -> Int8.t.

Axiom Cast_modulo : forall (a:Uint8.t),
  ((cast_modulo a) = (Int8.of_int (Bit_int8.normalize (Uint8.to_int a)))).

