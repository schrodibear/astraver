(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.
Require int.Abs.
Require int.EuclideanDivision.
Require int.ComputerDivision.
Require Enum_intf.
Require Powers_of_2.
Require Bit_enum_intf.

Parameter max: Z.

Parameter min: Z.

(* Why3 assumption *)
Definition normalize (x:Z): Z :=
  (min + (int.EuclideanDivision.mod1 (x - min)%Z ((max - min)%Z + 1%Z)%Z))%Z.

Axiom t : Type.
Parameter t_WhyType : WhyType t.
Existing Instance t_WhyType.

Parameter to_int: t -> Z.

Parameter in_bounds: Z -> Prop.

Parameter of_int: Z -> t.

Parameter infix_ls: t -> t -> Prop.

Parameter infix_lseq: t -> t -> Prop.

Parameter infix_gt: t -> t -> Prop.

Parameter infix_gteq: t -> t -> Prop.

Parameter size: Z.

Parameter signed: Prop.

Parameter of_int_modulo: Z -> t.

Parameter of_int_const: Z -> t.

Parameter infix_plpc: t -> t -> t.

Parameter infix_mnpc: t -> t -> t.

Parameter prefix_mnpc: t -> t.

Parameter infix_aspc: t -> t -> t.

Parameter infix_slpc: t -> t -> t.

Parameter infix_pcpc: t -> t -> t.

Axiom tt : Type.
Parameter tt_WhyType : WhyType tt.
Existing Instance tt_WhyType.

Parameter extend: t -> tt.

Parameter is_safe: tt -> Prop.

Parameter infix_plpctl: tt -> tt -> tt.

Parameter infix_mnpctl: tt -> tt -> tt.

Parameter prefix_mnpctl: tt -> tt.

Parameter infix_aspctl: tt -> tt -> tt.

Parameter infix_slpctl: tt -> tt -> tt.

Parameter infix_pcpctl: tt -> tt -> tt.

Parameter infix_et: t -> t -> t.

Parameter infix_brcf: t -> t -> t.

Parameter prefix_tl: t -> t.

Parameter infix_cf: t -> t -> t.

Parameter lsl: t -> t -> t.

Parameter lsl_modulo: t -> t -> t.

Parameter lsr: t -> t -> t.

Parameter asr: t -> t -> t.

Parameter lsl_modulo_: tt -> tt -> tt.

Parameter lt: t -> t -> Prop.

Parameter le: t -> t -> Prop.

Parameter gt: t -> t -> Prop.

Parameter ge: t -> t -> Prop.

Axiom Of_int_modulo : forall (n:Z),
  ((of_int_modulo n) = (of_int (normalize n))).

Axiom Add_modulo : forall (a:t) (b:t), ((infix_plpc a
  b) = (of_int (normalize ((to_int a) + (to_int b))%Z))).

Axiom Neg_modulo : forall (a:t),
  ((prefix_mnpc a) = (of_int (normalize (-(to_int a))%Z))).

Axiom Sub_modulo : forall (a:t) (b:t), ((infix_mnpc a
  b) = (of_int (normalize ((to_int a) - (to_int b))%Z))).

Axiom Mult_modulo : forall (a:t) (b:t), ((infix_aspc a
  b) = (of_int (normalize ((to_int a) * (to_int b))%Z))).

Axiom Div_modulo : forall (a:t) (b:t), ((infix_slpc a
  b) = (of_int (normalize (ZArith.BinInt.Z.quot (to_int a) (to_int b))))).

Axiom Mod_modulo : forall (a:t) (b:t), ((infix_pcpc a
  b) = (of_int (ZArith.BinInt.Z.rem (to_int a) (to_int b)))).

Axiom Size_pos : (0%Z < size)%Z.

Axiom Val_two_power_size : ((Powers_of_2.power2 size) = ((max - min)%Z + 1%Z)%Z).

Axiom Of_int_const : forall (n:Z), ((of_int_const n) = (of_int n)).

Axiom Of_int_def : forall (n:Z), (in_bounds n) ->
  ((of_int n) = (of_int_modulo n)).

Parameter to_uint: t -> Z.

Axiom To_uint : (signed) -> forall (a:t), ((lt a (of_int_const 0%Z)) ->
  ((to_int a) = ((to_uint a) - (Powers_of_2.power2 size))%Z)) /\ ((~ (lt a
  (of_int_const 0%Z))) -> ((to_int a) = ((to_uint a) - 0%Z)%Z)).

Parameter nth: t -> Z -> Prop.

Axiom Nth : forall (a:t), forall (n:Z), ((0%Z <= n)%Z /\ (n < size)%Z) ->
  ((nth a n) <-> (((0%Z <= (to_int a))%Z /\
  ((Powers_of_2.power2 n) <= (ZArith.BinInt.Z.rem (to_int a) (Powers_of_2.power2 (n + 1%Z)%Z)))%Z) \/
  (((to_int a) < 0%Z)%Z /\
  ((Powers_of_2.power2 n) <= (ZArith.BinInt.Z.rem (((max - min)%Z + 1%Z)%Z + (to_int a))%Z (Powers_of_2.power2 (n + 1%Z)%Z)))%Z))).

Axiom Lt_eq : forall (a:t) (b:t), (infix_ls a b) <-> (lt a b).

Axiom Le_eq : forall (a:t) (b:t), (infix_lseq a b) <-> (le a b).

Axiom Gt_eq : forall (a:t) (b:t), (infix_gt a b) <-> (gt a b).

Axiom Ge_eq : forall (a:t) (b:t), (infix_gteq a b) <-> (ge a b).

Axiom Nth_bw_and : forall (a:t) (b:t), forall (n:Z), ((0%Z <= n)%Z /\
  (n < size)%Z) -> ((nth (infix_et a b) n) <-> ((nth a n) /\ (nth b n))).

Axiom Nth_bw_or : forall (a:t) (b:t), forall (n:Z), ((0%Z <= n)%Z /\
  (n < size)%Z) -> ((nth (infix_brcf a b) n) <-> ((nth a n) \/ (nth b n))).

Axiom Nth_bw_xor : forall (a:t) (b:t), forall (n:Z), ((0%Z <= n)%Z /\
  (n < size)%Z) -> ((nth (infix_cf a b) n) <-> ~ ((nth a n) <-> (nth b n))).

Axiom Nth_bw_not : forall (a:t), forall (n:Z), ((0%Z <= n)%Z /\
  (n < size)%Z) -> ((nth (prefix_tl a) n) <-> ~ (nth a n)).

Axiom Lsl_def : forall (b:t), forall (s:t), (ge (lsl_modulo b s)
  (of_int_const 0%Z)) -> ((lsl b s) = (lsl_modulo b s)).

Axiom Lsr_nth_low : forall (b:t), forall (s:t), forall (n:Z),
  ((0%Z <= (to_int s))%Z /\ ((to_int s) < size)%Z) -> (((0%Z <= n)%Z /\
  (n < size)%Z) -> (((n + (to_int s))%Z < size)%Z -> ((nth (lsr b s) n) <->
  (nth b (n + (to_int s))%Z)))).

Axiom Lsr_nth_high : forall (b:t), forall (s:t), forall (n:Z),
  ((0%Z <= (to_int s))%Z /\ ((to_int s) < size)%Z) -> (((0%Z <= n)%Z /\
  (n < size)%Z) -> ((size <= (n + (to_int s))%Z)%Z -> ~ (nth (lsr b s) n))).

Axiom Asr_nth_low : forall (b:t), forall (s:t), forall (n:Z),
  ((0%Z <= (to_int s))%Z /\ ((to_int s) < size)%Z) -> (((0%Z <= n)%Z /\
  (n < size)%Z) -> (((0%Z <= (n + (to_int s))%Z)%Z /\
  ((n + (to_int s))%Z < size)%Z) -> ((nth (asr b s) n) <-> (nth b
  (n + (to_int s))%Z)))).

Axiom Asr_nth_high : forall (b:t), forall (s:t), forall (n:Z),
  ((0%Z <= (to_int s))%Z /\ ((to_int s) < size)%Z) -> (((0%Z <= n)%Z /\
  (n < size)%Z) -> ((size <= (n + (to_int s))%Z)%Z -> ((nth (asr b s) n) <->
  (nth b (size - 1%Z)%Z)))).

Axiom Lsl_modulo_nth_high : forall (b:t), forall (s:t), forall (n:Z),
  ((0%Z <= (to_int s))%Z /\ ((to_int s) < size)%Z) -> (((0%Z <= n)%Z /\
  (n < size)%Z) -> (((0%Z <= (n - (to_int s))%Z)%Z /\
  ((n - (to_int s))%Z < size)%Z) -> ((nth (lsl_modulo b s) n) <-> (nth b
  (n - (to_int s))%Z)))).

Axiom Lsl_modulo_nth_low : forall (b:t), forall (s:t), forall (n:Z),
  ((0%Z <= (to_int s))%Z /\ ((to_int s) < size)%Z) -> (((0%Z <= n)%Z /\
  (n < size)%Z) -> (((n - (to_int s))%Z < 0%Z)%Z -> ~ (nth (lsl_modulo b s)
  n))).

Axiom To_uint_lsr : (~ (signed)) -> forall (a:t), forall (n:t),
  (0%Z <= (to_int n))%Z -> ((to_int (lsr a
  n)) = (int.EuclideanDivision.div (to_int a)
  (Powers_of_2.power2 (to_int n)))).

Axiom To_uint_lsl_modulo : (~ (signed)) -> forall (a:t), forall (n:t),
  (0%Z <= (to_int n))%Z -> ((to_int (lsl_modulo a
  n)) = (int.EuclideanDivision.mod1 ((to_int a) * (Powers_of_2.power2 (to_int n)))%Z
  ((max - min)%Z + 1%Z)%Z)).
