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
Require Uint16.
Require Bit_int16.
Require Bit_uint16.

Parameter cast_modulo: Int16.t -> Uint16.t.

Axiom Cast_modulo : forall (a:Int16.t),
  ((cast_modulo a) = (Uint16.of_int (Bit_uint16.normalize (Int16.to_int a)))).

Parameter is_safe: Int16.t -> Prop.

Parameter bit_int16_as_bit_uint16: Int16.t -> Uint16.t -> Prop.

