(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import ZArith.
Require Import Rbase.
Require Import ZOdiv.
Require int.Int.
Require int.Abs.
Require int.ComputerDivision.
Require Jessie_memory_model.
Require real.Real.

(* Why3 assumption *)
Definition unit  := unit.

Parameter charP : Type.

Parameter int32 : Type.

Parameter int8 : Type.

Parameter padding : Type.

Parameter voidP : Type.

Parameter integer_of_int8: int8 -> Z.

(* Why3 assumption *)
Definition usAbsentTail(ep:(Jessie_memory_model.pointer charP)) (c:int8)
  (charP_charM_ep_1_at_L1:(Jessie_memory_model.memory charP int8)): Prop :=
  forall (p:(Jessie_memory_model.pointer charP)),
  (((Jessie_memory_model.sub_pointer (Jessie_memory_model.shift ep 1%Z)
  p) <= 0%Z)%Z /\ ((Jessie_memory_model.sub_pointer p ep) <= 0%Z)%Z) ->
  ~ ((integer_of_int8 (Jessie_memory_model.select charP_charM_ep_1_at_L1
  p)) = (integer_of_int8 c)).

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

Parameter integer_of_int32: int32 -> Z.

(* Why3 assumption *)
Definition eq_int32(x:int32) (y:int32): Prop :=
  ((integer_of_int32 x) = (integer_of_int32 y)).

(* Why3 assumption *)
Definition eq_int8(x:int8) (y:int8): Prop :=
  ((integer_of_int8 x) = (integer_of_int8 y)).

Parameter int32_of_integer: Z -> int32.

Axiom int32_coerce : forall (x:Z), (((-2147483648%Z)%Z <= x)%Z /\
  (x <= 2147483647%Z)%Z) -> ((integer_of_int32 (int32_of_integer x)) = x).

Axiom int32_extensionality : forall (x:int32), forall (y:int32),
  ((integer_of_int32 x) = (integer_of_int32 y)) -> (x = y).

Axiom int32_range : forall (x:int32),
  ((-2147483648%Z)%Z <= (integer_of_int32 x))%Z /\
  ((integer_of_int32 x) <= 2147483647%Z)%Z.

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

(* Why3 assumption *)
Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Implicit Arguments mk_ref.

(* Why3 assumption *)
Definition contents (a:Type)(v:(ref a)): a :=
  match v with
  | (mk_ref x) => x
  end.
Implicit Arguments contents.

Parameter eq_unit: unit -> unit -> Prop.

Parameter neq_unit: unit -> unit -> Prop.

Parameter eq_bool: bool -> bool -> Prop.

Parameter neq_bool: bool -> bool -> Prop.

Parameter lt_int: Z -> Z -> Prop.

Parameter le_int: Z -> Z -> Prop.

Parameter gt_int: Z -> Z -> Prop.

Parameter ge_int: Z -> Z -> Prop.

Parameter eq_int: Z -> Z -> Prop.

Parameter neq_int: Z -> Z -> Prop.

Parameter add_int: Z -> Z -> Z.

Parameter sub_int: Z -> Z -> Z.

Parameter mul_int: Z -> Z -> Z.

Parameter neg_int: Z -> Z.

(* Why3 assumption *)
Definition zwf_zero(a:Z) (b:Z): Prop := (0%Z <= b)%Z /\ (a < b)%Z.

Parameter lt_int_bool: Z -> Z -> bool.

Parameter le_int_bool: Z -> Z -> bool.

Parameter gt_int_bool: Z -> Z -> bool.

Parameter ge_int_bool: Z -> Z -> bool.

Parameter eq_int_bool: Z -> Z -> bool.

Parameter neq_int_bool: Z -> Z -> bool.

Axiom Lt_int_bool_axiom : forall (x:Z), forall (y:Z), ((lt_int_bool x
  y) = true) <-> (x < y)%Z.

Axiom Le_int_bool_axiom : forall (x:Z), forall (y:Z), ((le_int_bool x
  y) = true) <-> (x <= y)%Z.

Axiom Gt_int_bool_axiom : forall (x:Z), forall (y:Z), ((gt_int_bool x
  y) = true) <-> (y < x)%Z.

Axiom Ge_int_bool_axiom : forall (x:Z), forall (y:Z), ((ge_int_bool x
  y) = true) <-> (y <= x)%Z.

Axiom Eq_int_bool_axiom : forall (x:Z), forall (y:Z), ((eq_int_bool x
  y) = true) <-> (x = y).

Axiom Neq_int_bool_axiom : forall (x:Z), forall (y:Z), ((neq_int_bool x
  y) = true) <-> ~ (x = y).

Parameter abs_int: Z -> Z.

Axiom Abs_int_pos : forall (x:Z), (0%Z <= x)%Z -> ((Zabs x) = x).

Axiom Abs_int_neg : forall (x:Z), (x <= 0%Z)%Z -> ((Zabs x) = (-x)%Z).

Parameter int_max: Z -> Z -> Z.

Parameter int_min: Z -> Z -> Z.

Axiom Int_max_is_ge : forall (x:Z), forall (y:Z), (x <= (int_max x y))%Z /\
  (y <= (int_max x y))%Z.

Axiom Int_max_is_some : forall (x:Z), forall (y:Z), ((int_max x y) = x) \/
  ((int_max x y) = y).

Axiom Int_min_is_le : forall (x:Z), forall (y:Z), ((int_min x y) <= x)%Z /\
  ((int_min x y) <= y)%Z.

Axiom Int_min_is_some : forall (x:Z), forall (y:Z), ((int_min x y) = x) \/
  ((int_min x y) = y).

(* Why3 goal *)
Theorem WP_parameter_strprevchr_ensures_default : forall (endp:(Jessie_memory_model.pointer
  charP)) (c_0:int8) (startp:(Jessie_memory_model.pointer charP))
  (charP_endp_2_alloc_table:(Jessie_memory_model.alloc_table charP))
  (charP_charM_endp_2:(Jessie_memory_model.memory charP int8)),
  ((0%Z <= (Jessie_memory_model.sub_pointer endp startp))%Z /\
  (((Jessie_memory_model.offset_min charP_endp_2_alloc_table
  startp) <= 0%Z)%Z /\ ((Jessie_memory_model.sub_pointer endp
  startp) <= (Jessie_memory_model.offset_max charP_endp_2_alloc_table
  startp))%Z)) -> (usAbsentTail endp c_0 charP_charM_endp_2).
intros endp c_0 startp charP_endp_2_alloc_table charP_charM_endp_2
(h1,(h2,h3)).
red; intros p (h4,h5).
SearchAbout Jessie_memory_model.sub_pointer.
rewrite Jessie_memory_model.sub_pointer_shift_left in h4.
SearchAbout Jessie_memory_model.sub_pointer.
Qed.


