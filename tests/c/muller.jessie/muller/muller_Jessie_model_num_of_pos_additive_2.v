(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import ZArith.
Require Import Rbase.
Require int.Int.
Require Jessie_memory_model.

Parameter charP : Type.

Parameter int32 : Type.

Parameter int8 : Type.

Parameter intP : Type.

Parameter padding : Type.

Parameter voidP : Type.

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

Parameter integer_of_int8: int8 -> Z.

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

Parameter intP_tag: (Jessie_memory_model.tag_id intP).

Axiom intP_int : ((Jessie_memory_model.int_of_tag intP_tag) = 1%Z).

Parameter intP_of_pointer_address: (Jessie_memory_model.pointer unit) ->
  (Jessie_memory_model.pointer intP).

Axiom intP_of_pointer_address_of_pointer_addr : forall (p:(Jessie_memory_model.pointer
  intP)),
  (p = (intP_of_pointer_address (Jessie_memory_model.pointer_address p))).

Axiom intP_parenttag_bottom : (Jessie_memory_model.parenttag intP_tag
  (Jessie_memory_model.bottom_tag :(Jessie_memory_model.tag_id intP))).

Axiom intP_tags : forall (x:(Jessie_memory_model.pointer intP)),
  forall (intP_tag_table:(Jessie_memory_model.tag_table intP)),
  (Jessie_memory_model.instanceof intP_tag_table x intP_tag).

(* Why3 assumption *)
Definition left_valid_struct_charP(p:(Jessie_memory_model.pointer charP))
  (a:Z) (charP_alloc_table:(Jessie_memory_model.alloc_table charP)): Prop :=
  ((Jessie_memory_model.offset_min charP_alloc_table p) <= a)%Z.

(* Why3 assumption *)
Definition left_valid_struct_intP(p:(Jessie_memory_model.pointer intP)) (a:Z)
  (intP_alloc_table:(Jessie_memory_model.alloc_table intP)): Prop :=
  ((Jessie_memory_model.offset_min intP_alloc_table p) <= a)%Z.

(* Why3 assumption *)
Definition left_valid_struct_voidP(p:(Jessie_memory_model.pointer voidP))
  (a:Z) (voidP_alloc_table:(Jessie_memory_model.alloc_table voidP)): Prop :=
  ((Jessie_memory_model.offset_min voidP_alloc_table p) <= a)%Z.

Parameter num_of_pos: Z -> Z -> (Jessie_memory_model.pointer intP)
  -> (Jessie_memory_model.memory intP int32) -> Z.

Axiom pointer_addr_of_charP_of_pointer_address : forall (p:(Jessie_memory_model.pointer
  unit)),
  (p = (Jessie_memory_model.pointer_address (charP_of_pointer_address p))).

Axiom pointer_addr_of_intP_of_pointer_address : forall (p:(Jessie_memory_model.pointer
  unit)),
  (p = (Jessie_memory_model.pointer_address (intP_of_pointer_address p))).

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
Definition right_valid_struct_intP(p:(Jessie_memory_model.pointer intP))
  (b:Z) (intP_alloc_table:(Jessie_memory_model.alloc_table intP)): Prop :=
  (b <= (Jessie_memory_model.offset_max intP_alloc_table p))%Z.

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
Definition strict_valid_root_intP(p:(Jessie_memory_model.pointer intP)) (a:Z)
  (b:Z) (intP_alloc_table:(Jessie_memory_model.alloc_table intP)): Prop :=
  ((Jessie_memory_model.offset_min intP_alloc_table p) = a) /\
  ((Jessie_memory_model.offset_max intP_alloc_table p) = b).

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
Definition strict_valid_struct_intP(p:(Jessie_memory_model.pointer intP))
  (a:Z) (b:Z) (intP_alloc_table:(Jessie_memory_model.alloc_table
  intP)): Prop := ((Jessie_memory_model.offset_min intP_alloc_table
  p) = a) /\ ((Jessie_memory_model.offset_max intP_alloc_table p) = b).

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
Definition valid_root_intP(p:(Jessie_memory_model.pointer intP)) (a:Z) (b:Z)
  (intP_alloc_table:(Jessie_memory_model.alloc_table intP)): Prop :=
  ((Jessie_memory_model.offset_min intP_alloc_table p) <= a)%Z /\
  (b <= (Jessie_memory_model.offset_max intP_alloc_table p))%Z.

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
Definition valid_struct_intP(p:(Jessie_memory_model.pointer intP)) (a:Z)
  (b:Z) (intP_alloc_table:(Jessie_memory_model.alloc_table intP)): Prop :=
  ((Jessie_memory_model.offset_min intP_alloc_table p) <= a)%Z /\
  (b <= (Jessie_memory_model.offset_max intP_alloc_table p))%Z.

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

Axiom num_of_pos_empty : forall (intP_intM_t_1_at_L:(Jessie_memory_model.memory
  intP int32)), forall (i_0:Z), forall (j_0:Z),
  forall (t_0_0:(Jessie_memory_model.pointer intP)), (j_0 <= i_0)%Z ->
  ((num_of_pos i_0 j_0 t_0_0 intP_intM_t_1_at_L) = 0%Z).

Axiom num_of_pos_true_case : forall (intP_intM_t_1_at_L:(Jessie_memory_model.memory
  intP int32)), forall (i_1:Z), forall (j_1:Z),
  forall (t_1:(Jessie_memory_model.pointer intP)), ((i_1 < j_1)%Z /\
  (0%Z < (integer_of_int32 (Jessie_memory_model.select intP_intM_t_1_at_L
  (Jessie_memory_model.shift t_1 (j_1 - 1%Z)%Z))))%Z) -> ((num_of_pos i_1 j_1
  t_1 intP_intM_t_1_at_L) = ((num_of_pos i_1 (j_1 - 1%Z)%Z t_1
  intP_intM_t_1_at_L) + 1%Z)%Z).

Axiom num_of_pos_false_case : forall (intP_intM_t_1_at_L:(Jessie_memory_model.memory
  intP int32)), forall (i_2:Z), forall (j_2:Z),
  forall (t_2:(Jessie_memory_model.pointer intP)), ((i_2 < j_2)%Z /\
  ~ (0%Z < (integer_of_int32 (Jessie_memory_model.select intP_intM_t_1_at_L
  (Jessie_memory_model.shift t_2 (j_2 - 1%Z)%Z))))%Z) -> ((num_of_pos i_2 j_2
  t_2 intP_intM_t_1_at_L) = (num_of_pos i_2 (j_2 - 1%Z)%Z t_2
  intP_intM_t_1_at_L)).

Axiom num_of_pos_non_negative : forall (intP_intM_t_3_8_at_L:(Jessie_memory_model.memory
  intP int32)), forall (i_3:Z), forall (j_3:Z),
  forall (t_3:(Jessie_memory_model.pointer intP)), (0%Z <= (num_of_pos i_3
  j_3 t_3 intP_intM_t_3_8_at_L))%Z.

Open Scope Z_scope.
Import Jessie_memory_model.

(* Why3 goal *)
Theorem num_of_pos_additive : forall (intP_intM_t_4_9_at_L:(Jessie_memory_model.memory
  intP int32)), forall (i_4:Z), forall (j_4:Z), forall (k_1:Z),
  forall (t_4:(Jessie_memory_model.pointer intP)), ((i_4 <= j_4)%Z /\
  (j_4 <= k_1)%Z) -> ((num_of_pos i_4 k_1 t_4
  intP_intM_t_4_9_at_L) = ((num_of_pos i_4 j_4 t_4
  intP_intM_t_4_9_at_L) + (num_of_pos j_4 k_1 t_4 intP_intM_t_4_9_at_L))%Z).
(* YOU MAY EDIT THE PROOF BELOW *)
intros tMem i j k t (Hij,Hjk).
apply Zlt_lower_bound_ind with
  (P:= fun k => num_of_pos i k t tMem = 
         num_of_pos i j t tMem + num_of_pos j k t tMem)
  (z:=j); auto.
intros k0 Hind Hjk0.
assert (h:j=k0 \/ j < k0) by omega.
destruct h.
assert (h: num_of_pos j k0 t tMem = 0) by 
  (apply num_of_pos_empty; auto with zarith).
rewrite h; subst; auto with zarith.
destruct (Z_lt_dec 0 (integer_of_int32 (select tMem (shift t (k0 - 1))))).
rewrite num_of_pos_true_case at 1; intuition.
rewrite Hind; auto with zarith.
pattern (num_of_pos j k0 t tMem);
  rewrite num_of_pos_true_case; auto with zarith.
rewrite num_of_pos_false_case at 1; intuition.
rewrite Hind; auto with zarith.
pattern (num_of_pos j k0 t tMem);
  rewrite num_of_pos_false_case; auto with zarith.
Qed.


