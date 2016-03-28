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
Require Int16.
Require Bit_uint8.
Require Bit_int16.

Parameter cast_modulo: Uint8.t -> Int16.t.

Axiom Cast_modulo : forall (a:Uint8.t),
  ((cast_modulo a) = (Int16.of_int (Bit_int16.normalize (Uint8.to_int a)))).

Parameter is_safe: Uint8.t -> Prop.

Parameter bit_uint8_as_bit_int16: Int16.t -> Uint8.t -> Uint8.t -> Prop.

