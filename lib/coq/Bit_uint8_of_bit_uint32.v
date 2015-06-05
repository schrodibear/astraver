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
Require Uint8.
Require Uint32.
Require Bit_uint8.
Require Bit_uint32.

Parameter cast_modulo: Uint32.t -> Uint8.t.

Axiom Cast_modulo : forall (a:Uint32.t),
  ((cast_modulo a) = (Uint8.of_int (Bit_uint8.normalize (Uint32.to_int a)))).

