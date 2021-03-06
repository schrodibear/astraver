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
Require Uint32.
Require Uint64.
Require Bit_uint32.
Require Bit_uint64.

Parameter cast_modulo: Uint32.t -> Uint64.t.

Axiom Cast_modulo : forall (a:Uint32.t),
  ((cast_modulo a) = (Uint64.of_int (Bit_uint64.normalize (Uint32.to_int a)))).

Parameter is_safe: Uint32.t -> Prop.

Parameter bit_uint32_as_bit_uint64: Uint64.t -> Uint32.t -> Uint32.t -> Prop.

