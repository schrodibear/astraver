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
Require Int64.
Require Uint64.
Require Bit_int64.
Require Bit_uint64.

Parameter cast_modulo: Uint64.t -> Int64.t.

Axiom Cast_modulo : forall (a:Uint64.t),
  ((cast_modulo a) = (Int64.of_int (Bit_int64.normalize (Uint64.to_int a)))).

