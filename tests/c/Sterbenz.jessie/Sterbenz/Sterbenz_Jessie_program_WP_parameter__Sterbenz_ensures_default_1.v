(* This file is generated by Why3's Coq 8.4 driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require Import Rbasic_fun.
Require Import ZOdiv.
Require BuiltIn.
Require int.Int.
Require int.Abs.
Require int.ComputerDivision.
Require bool.Bool.
Require real.Real.
Require real.RealInfix.
Require real.Abs.
Require real.FromInt.
Require floating_point.Rounding.
Require floating_point.SingleFormat.
Require floating_point.DoubleFormat.
Require floating_point.Single.
Require floating_point.Double.
Require Jessie_memory_model.

(* Why3 assumption *)
Definition unit := unit.

Axiom charP : Type.
Parameter charP_WhyType : WhyType charP.
Existing Instance charP_WhyType.

Axiom int8 : Type.
Parameter int8_WhyType : WhyType int8.
Existing Instance int8_WhyType.

Axiom padding : Type.
Parameter padding_WhyType : WhyType padding.
Existing Instance padding_WhyType.

Axiom uint8 : Type.
Parameter uint8_WhyType : WhyType uint8.
Existing Instance uint8_WhyType.

Axiom unsigned_charP : Type.
Parameter unsigned_charP_WhyType : WhyType unsigned_charP.
Existing Instance unsigned_charP_WhyType.

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
Definition eq_int8 (x:int8) (y:int8): Prop :=
  ((integer_of_int8 x) = (integer_of_int8 y)).

Parameter integer_of_uint8: uint8 -> Z.

(* Why3 assumption *)
Definition eq_uint8 (x:uint8) (y:uint8): Prop :=
  ((integer_of_uint8 x) = (integer_of_uint8 y)).

Parameter int8_of_integer: Z -> int8.

Axiom int8_coerce : forall (x:Z), (((-128%Z)%Z <= x)%Z /\ (x <= 127%Z)%Z) ->
  ((integer_of_int8 (int8_of_integer x)) = x).

Axiom int8_extensionality : forall (x:int8), forall (y:int8),
  ((integer_of_int8 x) = (integer_of_int8 y)) -> (x = y).

Axiom int8_range : forall (x:int8), ((-128%Z)%Z <= (integer_of_int8 x))%Z /\
  ((integer_of_int8 x) <= 127%Z)%Z.

(* Why3 assumption *)
Definition left_valid_struct_charP (p:(Jessie_memory_model.pointer charP))
  (a:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table charP)): Prop :=
  ((Jessie_memory_model.offset_min charP_alloc_table p) <= a)%Z.

(* Why3 assumption *)
Definition left_valid_struct_unsigned_charP (p:(Jessie_memory_model.pointer
  unsigned_charP)) (a:Z)
  (unsigned_charP_alloc_table:(Jessie_memory_model.alloc_table
  unsigned_charP)): Prop :=
  ((Jessie_memory_model.offset_min unsigned_charP_alloc_table p) <= a)%Z.

(* Why3 assumption *)
Definition left_valid_struct_voidP (p:(Jessie_memory_model.pointer voidP))
  (a:Z) (voidP_alloc_table:(Jessie_memory_model.alloc_table voidP)): Prop :=
  ((Jessie_memory_model.offset_min voidP_alloc_table p) <= a)%Z.

Axiom pointer_addr_of_charP_of_pointer_address : forall (p:(Jessie_memory_model.pointer
  unit)),
  (p = (Jessie_memory_model.pointer_address (charP_of_pointer_address p))).

Parameter unsigned_charP_of_pointer_address: (Jessie_memory_model.pointer
  unit) -> (Jessie_memory_model.pointer unsigned_charP).

Axiom pointer_addr_of_unsigned_charP_of_pointer_address : forall (p:(Jessie_memory_model.pointer
  unit)),
  (p = (Jessie_memory_model.pointer_address (unsigned_charP_of_pointer_address p))).

Parameter voidP_of_pointer_address: (Jessie_memory_model.pointer unit) ->
  (Jessie_memory_model.pointer voidP).

Axiom pointer_addr_of_voidP_of_pointer_address : forall (p:(Jessie_memory_model.pointer
  unit)),
  (p = (Jessie_memory_model.pointer_address (voidP_of_pointer_address p))).

(* Why3 assumption *)
Definition right_valid_struct_charP (p:(Jessie_memory_model.pointer charP))
  (b:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table charP)): Prop :=
  (b <= (Jessie_memory_model.offset_max charP_alloc_table p))%Z.

(* Why3 assumption *)
Definition right_valid_struct_unsigned_charP (p:(Jessie_memory_model.pointer
  unsigned_charP)) (b:Z)
  (unsigned_charP_alloc_table:(Jessie_memory_model.alloc_table
  unsigned_charP)): Prop :=
  (b <= (Jessie_memory_model.offset_max unsigned_charP_alloc_table p))%Z.

(* Why3 assumption *)
Definition right_valid_struct_voidP (p:(Jessie_memory_model.pointer voidP))
  (b:Z) (voidP_alloc_table:(Jessie_memory_model.alloc_table voidP)): Prop :=
  (b <= (Jessie_memory_model.offset_max voidP_alloc_table p))%Z.

(* Why3 assumption *)
Definition strict_valid_root_charP (p:(Jessie_memory_model.pointer charP))
  (a:Z) (b:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table
  charP)): Prop := ((Jessie_memory_model.offset_min charP_alloc_table
  p) = a) /\ ((Jessie_memory_model.offset_max charP_alloc_table p) = b).

(* Why3 assumption *)
Definition strict_valid_root_unsigned_charP (p:(Jessie_memory_model.pointer
  unsigned_charP)) (a:Z) (b:Z)
  (unsigned_charP_alloc_table:(Jessie_memory_model.alloc_table
  unsigned_charP)): Prop :=
  ((Jessie_memory_model.offset_min unsigned_charP_alloc_table p) = a) /\
  ((Jessie_memory_model.offset_max unsigned_charP_alloc_table p) = b).

(* Why3 assumption *)
Definition strict_valid_root_voidP (p:(Jessie_memory_model.pointer voidP))
  (a:Z) (b:Z) (voidP_alloc_table:(Jessie_memory_model.alloc_table
  voidP)): Prop := ((Jessie_memory_model.offset_min voidP_alloc_table
  p) = a) /\ ((Jessie_memory_model.offset_max voidP_alloc_table p) = b).

(* Why3 assumption *)
Definition strict_valid_struct_charP (p:(Jessie_memory_model.pointer charP))
  (a:Z) (b:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table
  charP)): Prop := ((Jessie_memory_model.offset_min charP_alloc_table
  p) = a) /\ ((Jessie_memory_model.offset_max charP_alloc_table p) = b).

(* Why3 assumption *)
Definition strict_valid_struct_unsigned_charP (p:(Jessie_memory_model.pointer
  unsigned_charP)) (a:Z) (b:Z)
  (unsigned_charP_alloc_table:(Jessie_memory_model.alloc_table
  unsigned_charP)): Prop :=
  ((Jessie_memory_model.offset_min unsigned_charP_alloc_table p) = a) /\
  ((Jessie_memory_model.offset_max unsigned_charP_alloc_table p) = b).

(* Why3 assumption *)
Definition strict_valid_struct_voidP (p:(Jessie_memory_model.pointer voidP))
  (a:Z) (b:Z) (voidP_alloc_table:(Jessie_memory_model.alloc_table
  voidP)): Prop := ((Jessie_memory_model.offset_min voidP_alloc_table
  p) = a) /\ ((Jessie_memory_model.offset_max voidP_alloc_table p) = b).

Parameter uint8_of_integer: Z -> uint8.

Axiom uint8_coerce : forall (x:Z), ((0%Z <= x)%Z /\ (x <= 255%Z)%Z) ->
  ((integer_of_uint8 (uint8_of_integer x)) = x).

Axiom uint8_extensionality : forall (x:uint8), forall (y:uint8),
  ((integer_of_uint8 x) = (integer_of_uint8 y)) -> (x = y).

Axiom uint8_range : forall (x:uint8), (0%Z <= (integer_of_uint8 x))%Z /\
  ((integer_of_uint8 x) <= 255%Z)%Z.

Parameter unsigned_charP_tag: (Jessie_memory_model.tag_id unsigned_charP).

Axiom unsigned_charP_int : ((Jessie_memory_model.int_of_tag unsigned_charP_tag) = 1%Z).

Axiom unsigned_charP_of_pointer_address_of_pointer_addr : forall (p:(Jessie_memory_model.pointer
  unsigned_charP)),
  (p = (unsigned_charP_of_pointer_address (Jessie_memory_model.pointer_address p))).

Axiom unsigned_charP_parenttag_bottom : (Jessie_memory_model.parenttag
  unsigned_charP_tag
  (Jessie_memory_model.bottom_tag :(Jessie_memory_model.tag_id
  unsigned_charP))).

Axiom unsigned_charP_tags : forall (x:(Jessie_memory_model.pointer
  unsigned_charP)),
  forall (unsigned_charP_tag_table:(Jessie_memory_model.tag_table
  unsigned_charP)), (Jessie_memory_model.instanceof unsigned_charP_tag_table
  x unsigned_charP_tag).

(* Why3 assumption *)
Definition valid_root_charP (p:(Jessie_memory_model.pointer charP)) (a:Z)
  (b:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table charP)): Prop :=
  ((Jessie_memory_model.offset_min charP_alloc_table p) <= a)%Z /\
  (b <= (Jessie_memory_model.offset_max charP_alloc_table p))%Z.

(* Why3 assumption *)
Definition valid_root_unsigned_charP (p:(Jessie_memory_model.pointer
  unsigned_charP)) (a:Z) (b:Z)
  (unsigned_charP_alloc_table:(Jessie_memory_model.alloc_table
  unsigned_charP)): Prop :=
  ((Jessie_memory_model.offset_min unsigned_charP_alloc_table p) <= a)%Z /\
  (b <= (Jessie_memory_model.offset_max unsigned_charP_alloc_table p))%Z.

(* Why3 assumption *)
Definition valid_root_voidP (p:(Jessie_memory_model.pointer voidP)) (a:Z)
  (b:Z) (voidP_alloc_table:(Jessie_memory_model.alloc_table voidP)): Prop :=
  ((Jessie_memory_model.offset_min voidP_alloc_table p) <= a)%Z /\
  (b <= (Jessie_memory_model.offset_max voidP_alloc_table p))%Z.

(* Why3 assumption *)
Definition valid_struct_charP (p:(Jessie_memory_model.pointer charP)) (a:Z)
  (b:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table charP)): Prop :=
  ((Jessie_memory_model.offset_min charP_alloc_table p) <= a)%Z /\
  (b <= (Jessie_memory_model.offset_max charP_alloc_table p))%Z.

(* Why3 assumption *)
Definition valid_struct_unsigned_charP (p:(Jessie_memory_model.pointer
  unsigned_charP)) (a:Z) (b:Z)
  (unsigned_charP_alloc_table:(Jessie_memory_model.alloc_table
  unsigned_charP)): Prop :=
  ((Jessie_memory_model.offset_min unsigned_charP_alloc_table p) <= a)%Z /\
  (b <= (Jessie_memory_model.offset_max unsigned_charP_alloc_table p))%Z.

(* Why3 assumption *)
Definition valid_struct_voidP (p:(Jessie_memory_model.pointer voidP)) (a:Z)
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
Inductive ref (a:Type) {a_WT:WhyType a} :=
  | mk_ref : a -> ref a.
Axiom ref_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (ref a).
Existing Instance ref_WhyType.
Implicit Arguments mk_ref [[a] [a_WT]].

(* Why3 assumption *)
Definition contents {a:Type} {a_WT:WhyType a} (v:(ref a)): a :=
  match v with
  | (mk_ref x) => x
  end.

(* Why3 assumption *)
Definition single_of_double_post (m:floating_point.Rounding.mode)
  (x:floating_point.DoubleFormat.double)
  (res:floating_point.SingleFormat.single): Prop :=
  ((floating_point.Single.value res) = (floating_point.Single.round m
  (floating_point.Double.value x))) /\
  (((floating_point.Single.exact res) = (floating_point.Double.exact x)) /\
  ((floating_point.Single.model res) = (floating_point.Double.model x))).

(* Why3 assumption *)
Definition double_of_single_post (x:floating_point.SingleFormat.single)
  (res:floating_point.DoubleFormat.double): Prop :=
  ((floating_point.Double.value res) = (floating_point.Single.value x)) /\
  (((floating_point.Double.exact res) = (floating_point.Single.exact x)) /\
  ((floating_point.Double.model res) = (floating_point.Single.model x))).

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
Definition zwf_zero (a:Z) (b:Z): Prop := (0%Z <= b)%Z /\ (a < b)%Z.

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


Require Import Fprop_Sterbenz.

(* Why3 goal *)
Theorem WP_parameter__Sterbenz_ensures_default : forall (x_0:floating_point.SingleFormat.single)
  (y:floating_point.SingleFormat.single),
  (((Rdiv (floating_point.Single.value y) 2%R)%R <= (floating_point.Single.value x_0))%R /\
  ((floating_point.Single.value x_0) <= (2%R * (floating_point.Single.value y))%R)%R) ->
  ((0%R <= (floating_point.Single.value y))%R ->
  ((0%R <= (floating_point.Single.value x_0))%R ->
  forall (o:floating_point.SingleFormat.single),
  (floating_point.Single.sub_post floating_point.Rounding.NearestTiesToEven
  x_0 y o) -> forall (us_retres:floating_point.SingleFormat.single),
  (us_retres = o) -> forall (return1:floating_point.SingleFormat.single),
  (return1 = us_retres) ->
  ((floating_point.Single.value return1) = ((floating_point.Single.value x_0) - (floating_point.Single.value y))%R))).
Proof with auto with typeclass_instances.
intros x y H1 h1 h2 r Hr r1 Hr1 r2 Hr2; subst.
destruct Hr as (H,_); rewrite H.
apply Fcore_generic_fmt.round_generic...
apply sterbenz...
apply Fappli_IEEE.generic_format_B2R.
apply Fappli_IEEE.generic_format_B2R.
Qed.

