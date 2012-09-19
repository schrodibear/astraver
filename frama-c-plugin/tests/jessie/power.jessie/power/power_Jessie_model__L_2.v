(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require Import Rfunctions.
Require BuiltIn.
Require int.Int.
Require real.Real.
Require real.PowerInt.
Require Jessie_memory_model.

Axiom charP : Type.
Parameter charP_WhyType : WhyType charP.
Existing Instance charP_WhyType.

Axiom int8 : Type.
Parameter int8_WhyType : WhyType int8.
Existing Instance int8_WhyType.

Axiom padding : Type.
Parameter padding_WhyType : WhyType padding.
Existing Instance padding_WhyType.

Axiom voidP : Type.
Parameter voidP_WhyType : WhyType voidP.
Existing Instance voidP_WhyType.

Parameter charP_tag: (Jessie_memory_model.tag_id charP).

Axiom charP_int : ((Jessie_memory_model.int_of_tag charP_tag) = 1%Z).

Parameter charP_of_pointer_address: (Jessie_memory_model.pointer unit) ->
  (Jessie_memory_model.pointer charP).

Axiom charP_of_pointer_address_of_pointer_addr : forall (p:(Jessie_memory_model.pointer
  charP)),
  (p = (charP_of_pointer_address (Jessie_memory_model.pointer_address p))).

Axiom charP_parenttag_bottom : (Jessie_memory_model.parenttag charP_tag
  (Jessie_memory_model.bottom_tag :(Jessie_memory_model.tag_id charP))).

Axiom charP_tags : forall (x:(Jessie_memory_model.pointer charP)),
  forall (charP_tag_table:(Jessie_memory_model.tag_table charP)),
  (Jessie_memory_model.instanceof charP_tag_table x charP_tag).

Parameter integer_of_int8: int8 -> Z.

(* Why3 assumption *)
Definition eq_int8(x:int8) (y:int8): Prop :=
  ((integer_of_int8 x) = (integer_of_int8 y)).

Parameter int8_of_integer: Z -> int8.

Axiom int8_coerce : forall (x:Z), (((-128%Z)%Z <= x)%Z /\ (x <= 127%Z)%Z) ->
  ((integer_of_int8 (int8_of_integer x)) = x).

Axiom int8_extensionality : forall (x:int8), forall (y:int8),
  ((integer_of_int8 x) = (integer_of_int8 y)) -> (x = y).

Axiom int8_range : forall (x:int8), ((-128%Z)%Z <= (integer_of_int8 x))%Z /\
  ((integer_of_int8 x) <= 127%Z)%Z.

(* Why3 assumption *)
Definition left_valid_struct_charP(p:(Jessie_memory_model.pointer charP))
  (a:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table charP)): Prop :=
  ((Jessie_memory_model.offset_min charP_alloc_table p) <= a)%Z.

(* Why3 assumption *)
Definition left_valid_struct_voidP(p:(Jessie_memory_model.pointer voidP))
  (a:Z) (voidP_alloc_table:(Jessie_memory_model.alloc_table voidP)): Prop :=
  ((Jessie_memory_model.offset_min voidP_alloc_table p) <= a)%Z.

Axiom pointer_addr_of_charP_of_pointer_address : forall (p:(Jessie_memory_model.pointer
  unit)),
  (p = (Jessie_memory_model.pointer_address (charP_of_pointer_address p))).

Parameter voidP_of_pointer_address: (Jessie_memory_model.pointer unit) ->
  (Jessie_memory_model.pointer voidP).

Axiom pointer_addr_of_voidP_of_pointer_address : forall (p:(Jessie_memory_model.pointer
  unit)),
  (p = (Jessie_memory_model.pointer_address (voidP_of_pointer_address p))).

Parameter power: R -> Z -> R.

(* Why3 assumption *)
Definition right_valid_struct_charP(p:(Jessie_memory_model.pointer charP))
  (b:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table charP)): Prop :=
  (b <= (Jessie_memory_model.offset_max charP_alloc_table p))%Z.

(* Why3 assumption *)
Definition right_valid_struct_voidP(p:(Jessie_memory_model.pointer voidP))
  (b:Z) (voidP_alloc_table:(Jessie_memory_model.alloc_table voidP)): Prop :=
  (b <= (Jessie_memory_model.offset_max voidP_alloc_table p))%Z.

(* Why3 assumption *)
Definition strict_valid_root_charP(p:(Jessie_memory_model.pointer charP))
  (a:Z) (b:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table
  charP)): Prop := ((Jessie_memory_model.offset_min charP_alloc_table
  p) = a) /\ ((Jessie_memory_model.offset_max charP_alloc_table p) = b).

(* Why3 assumption *)
Definition strict_valid_root_voidP(p:(Jessie_memory_model.pointer voidP))
  (a:Z) (b:Z) (voidP_alloc_table:(Jessie_memory_model.alloc_table
  voidP)): Prop := ((Jessie_memory_model.offset_min voidP_alloc_table
  p) = a) /\ ((Jessie_memory_model.offset_max voidP_alloc_table p) = b).

(* Why3 assumption *)
Definition strict_valid_struct_charP(p:(Jessie_memory_model.pointer charP))
  (a:Z) (b:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table
  charP)): Prop := ((Jessie_memory_model.offset_min charP_alloc_table
  p) = a) /\ ((Jessie_memory_model.offset_max charP_alloc_table p) = b).

(* Why3 assumption *)
Definition strict_valid_struct_voidP(p:(Jessie_memory_model.pointer voidP))
  (a:Z) (b:Z) (voidP_alloc_table:(Jessie_memory_model.alloc_table
  voidP)): Prop := ((Jessie_memory_model.offset_min voidP_alloc_table
  p) = a) /\ ((Jessie_memory_model.offset_max voidP_alloc_table p) = b).

(* Why3 assumption *)
Definition valid_root_charP(p:(Jessie_memory_model.pointer charP)) (a:Z)
  (b:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table charP)): Prop :=
  ((Jessie_memory_model.offset_min charP_alloc_table p) <= a)%Z /\
  (b <= (Jessie_memory_model.offset_max charP_alloc_table p))%Z.

(* Why3 assumption *)
Definition valid_root_voidP(p:(Jessie_memory_model.pointer voidP)) (a:Z)
  (b:Z) (voidP_alloc_table:(Jessie_memory_model.alloc_table voidP)): Prop :=
  ((Jessie_memory_model.offset_min voidP_alloc_table p) <= a)%Z /\
  (b <= (Jessie_memory_model.offset_max voidP_alloc_table p))%Z.

(* Why3 assumption *)
Definition valid_struct_charP(p:(Jessie_memory_model.pointer charP)) (a:Z)
  (b:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table charP)): Prop :=
  ((Jessie_memory_model.offset_min charP_alloc_table p) <= a)%Z /\
  (b <= (Jessie_memory_model.offset_max charP_alloc_table p))%Z.

(* Why3 assumption *)
Definition valid_struct_voidP(p:(Jessie_memory_model.pointer voidP)) (a:Z)
  (b:Z) (voidP_alloc_table:(Jessie_memory_model.alloc_table voidP)): Prop :=
  ((Jessie_memory_model.offset_min voidP_alloc_table p) <= a)%Z /\
  (b <= (Jessie_memory_model.offset_max voidP_alloc_table p))%Z.

Parameter voidP_tag: (Jessie_memory_model.tag_id voidP).

Axiom voidP_int : ((Jessie_memory_model.int_of_tag voidP_tag) = 1%Z).

Axiom voidP_of_pointer_address_of_pointer_addr : forall (p:(Jessie_memory_model.pointer
  voidP)),
  (p = (voidP_of_pointer_address (Jessie_memory_model.pointer_address p))).

Axiom voidP_parenttag_bottom : (Jessie_memory_model.parenttag voidP_tag
  (Jessie_memory_model.bottom_tag :(Jessie_memory_model.tag_id voidP))).

Axiom voidP_tags : forall (x:(Jessie_memory_model.pointer voidP)),
  forall (voidP_tag_table:(Jessie_memory_model.tag_table voidP)),
  (Jessie_memory_model.instanceof voidP_tag_table x voidP_tag).

Open Scope Z_scope.

(* Why3 goal *)
Theorem usL : ((powerRZ 2%R 2%Z) = 4%R).
simpl.
now rewrite Rmult_1_r.
Qed.


