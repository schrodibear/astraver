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
Require Uint16.

(* Why3 assumption *)
Definition normalize (x:Z): Z :=
  (0%Z + (int.EuclideanDivision.mod1 (x - 0%Z)%Z
  ((65535%Z - 0%Z)%Z + 1%Z)%Z))%Z.

Parameter of_int_modulo: Z -> Uint16.t.

Parameter of_int_const: Z -> Uint16.t.

Parameter infix_plpc: Uint16.t -> Uint16.t -> Uint16.t.

Parameter infix_mnpc: Uint16.t -> Uint16.t -> Uint16.t.

Parameter prefix_mnpc: Uint16.t -> Uint16.t.

Parameter infix_aspc: Uint16.t -> Uint16.t -> Uint16.t.

Parameter infix_slpc: Uint16.t -> Uint16.t -> Uint16.t.

Parameter infix_pcpc: Uint16.t -> Uint16.t -> Uint16.t.

Axiom tt : Type.
Parameter tt_WhyType : WhyType tt.
Existing Instance tt_WhyType.

Parameter extend: Uint16.t -> tt.

Parameter is_safe: tt -> Prop.

Parameter infix_plpctl: tt -> tt -> tt.

Parameter infix_mnpctl: tt -> tt -> tt.

Parameter prefix_mnpctl: tt -> tt.

Parameter infix_aspctl: tt -> tt -> tt.

Parameter infix_slpctl: tt -> tt -> tt.

Parameter infix_pcpctl: tt -> tt -> tt.

Parameter infix_et: Uint16.t -> Uint16.t -> Uint16.t.

Parameter infix_brcf: Uint16.t -> Uint16.t -> Uint16.t.

Parameter prefix_tl: Uint16.t -> Uint16.t.

Parameter infix_cf: Uint16.t -> Uint16.t -> Uint16.t.

Parameter lsl: Uint16.t -> Uint16.t -> Uint16.t.

Parameter lsl_modulo: Uint16.t -> Uint16.t -> Uint16.t.

Parameter lsr: Uint16.t -> Uint16.t -> Uint16.t.

Parameter asr: Uint16.t -> Uint16.t -> Uint16.t.

Parameter lsl_modulo_: tt -> tt -> tt.

Parameter lt: Uint16.t -> Uint16.t -> Prop.

Parameter le: Uint16.t -> Uint16.t -> Prop.

Parameter gt: Uint16.t -> Uint16.t -> Prop.

Parameter ge: Uint16.t -> Uint16.t -> Prop.

Axiom Of_int_modulo : forall (n:Z),
  ((of_int_modulo n) = (Uint16.of_int (normalize n))).

Axiom Add_modulo : forall (a:Uint16.t) (b:Uint16.t), ((infix_plpc a
  b) = (Uint16.of_int (normalize ((Uint16.to_int a) + (Uint16.to_int b))%Z))).

Axiom Neg_modulo : forall (a:Uint16.t),
  ((prefix_mnpc a) = (Uint16.of_int (normalize (-(Uint16.to_int a))%Z))).

Axiom Sub_modulo : forall (a:Uint16.t) (b:Uint16.t), ((infix_mnpc a
  b) = (Uint16.of_int (normalize ((Uint16.to_int a) - (Uint16.to_int b))%Z))).

Axiom Mult_modulo : forall (a:Uint16.t) (b:Uint16.t), ((infix_aspc a
  b) = (Uint16.of_int (normalize ((Uint16.to_int a) * (Uint16.to_int b))%Z))).

Axiom Div_modulo : forall (a:Uint16.t) (b:Uint16.t), ((infix_slpc a
  b) = (Uint16.of_int (normalize (ZArith.BinInt.Z.quot (Uint16.to_int a) (Uint16.to_int b))))).

Axiom Mod_modulo : forall (a:Uint16.t) (b:Uint16.t), ((infix_pcpc a
  b) = (Uint16.of_int (ZArith.BinInt.Z.rem (Uint16.to_int a) (Uint16.to_int b)))).

Axiom Val_two_power_size : ((Powers_of_2.power2 16%Z) = ((65535%Z - 0%Z)%Z + 1%Z)%Z).

Axiom Of_int_const : forall (n:Z), ((of_int_const n) = (Uint16.of_int n)).

Axiom Of_int_def : forall (n:Z), (Uint16.in_bounds n) ->
  ((Uint16.of_int n) = (of_int_modulo n)).

Parameter to_uint: Uint16.t -> Z.

Axiom To_uint : True.

Parameter nth: Uint16.t -> Z -> Prop.

Axiom Nth : forall (a:Uint16.t), forall (n:Z), ((0%Z <= n)%Z /\
  (n < 16%Z)%Z) -> ((nth a n) <-> (((0%Z <= (Uint16.to_int a))%Z /\
  ((Powers_of_2.power2 n) <= (ZArith.BinInt.Z.rem (Uint16.to_int a) (Powers_of_2.power2 (n + 1%Z)%Z)))%Z) \/
  (((Uint16.to_int a) < 0%Z)%Z /\
  ((Powers_of_2.power2 n) <= (ZArith.BinInt.Z.rem (((65535%Z - 0%Z)%Z + 1%Z)%Z + (Uint16.to_int a))%Z (Powers_of_2.power2 (n + 1%Z)%Z)))%Z))).

Axiom Lt_eq : forall (a:Uint16.t) (b:Uint16.t), (Uint16.infix_ls a b) <-> (lt
  a b).

Axiom Le_eq : forall (a:Uint16.t) (b:Uint16.t), (Uint16.infix_lseq a b) <->
  (le a b).

Axiom Gt_eq : forall (a:Uint16.t) (b:Uint16.t), (Uint16.infix_gt a b) <-> (gt
  a b).

Axiom Ge_eq : forall (a:Uint16.t) (b:Uint16.t), (Uint16.infix_gteq a b) <->
  (ge a b).

Axiom Nth_bw_and : forall (a:Uint16.t) (b:Uint16.t), forall (n:Z),
  ((0%Z <= n)%Z /\ (n < 16%Z)%Z) -> ((nth (infix_et a b) n) <-> ((nth a n) /\
  (nth b n))).

Axiom Nth_bw_or : forall (a:Uint16.t) (b:Uint16.t), forall (n:Z),
  ((0%Z <= n)%Z /\ (n < 16%Z)%Z) -> ((nth (infix_brcf a b) n) <-> ((nth a
  n) \/ (nth b n))).

Axiom Nth_bw_xor : forall (a:Uint16.t) (b:Uint16.t), forall (n:Z),
  ((0%Z <= n)%Z /\ (n < 16%Z)%Z) -> ((nth (infix_cf a b) n) <-> ~ ((nth a
  n) <-> (nth b n))).

Axiom Nth_bw_not : forall (a:Uint16.t), forall (n:Z), ((0%Z <= n)%Z /\
  (n < 16%Z)%Z) -> ((nth (prefix_tl a) n) <-> ~ (nth a n)).

Axiom Lsl_def : forall (b:Uint16.t), forall (s:Uint16.t), (ge (lsl_modulo b
  s) (of_int_const 0%Z)) -> ((lsl b s) = (lsl_modulo b s)).

Axiom Lsr_nth_low : forall (b:Uint16.t), forall (s:Uint16.t), forall (n:Z),
  ((0%Z <= (Uint16.to_int s))%Z /\ ((Uint16.to_int s) < 16%Z)%Z) ->
  (((0%Z <= n)%Z /\ (n < 16%Z)%Z) -> (((n + (Uint16.to_int s))%Z < 16%Z)%Z ->
  ((nth (lsr b s) n) <-> (nth b (n + (Uint16.to_int s))%Z)))).

Axiom Lsr_nth_high : forall (b:Uint16.t), forall (s:Uint16.t), forall (n:Z),
  ((0%Z <= (Uint16.to_int s))%Z /\ ((Uint16.to_int s) < 16%Z)%Z) ->
  (((0%Z <= n)%Z /\ (n < 16%Z)%Z) ->
  ((16%Z <= (n + (Uint16.to_int s))%Z)%Z -> ~ (nth (lsr b s) n))).

Axiom Asr_nth_low : forall (b:Uint16.t), forall (s:Uint16.t), forall (n:Z),
  ((0%Z <= (Uint16.to_int s))%Z /\ ((Uint16.to_int s) < 16%Z)%Z) ->
  (((0%Z <= n)%Z /\ (n < 16%Z)%Z) ->
  (((0%Z <= (n + (Uint16.to_int s))%Z)%Z /\
  ((n + (Uint16.to_int s))%Z < 16%Z)%Z) -> ((nth (asr b s) n) <-> (nth b
  (n + (Uint16.to_int s))%Z)))).

Axiom Asr_nth_high : forall (b:Uint16.t), forall (s:Uint16.t), forall (n:Z),
  ((0%Z <= (Uint16.to_int s))%Z /\ ((Uint16.to_int s) < 16%Z)%Z) ->
  (((0%Z <= n)%Z /\ (n < 16%Z)%Z) ->
  ((16%Z <= (n + (Uint16.to_int s))%Z)%Z -> ((nth (asr b s) n) <-> (nth b
  (16%Z - 1%Z)%Z)))).

Axiom Lsl_modulo_nth_high : forall (b:Uint16.t), forall (s:Uint16.t),
  forall (n:Z), ((0%Z <= (Uint16.to_int s))%Z /\
  ((Uint16.to_int s) < 16%Z)%Z) -> (((0%Z <= n)%Z /\ (n < 16%Z)%Z) ->
  (((0%Z <= (n - (Uint16.to_int s))%Z)%Z /\
  ((n - (Uint16.to_int s))%Z < 16%Z)%Z) -> ((nth (lsl_modulo b s) n) <-> (nth
  b (n - (Uint16.to_int s))%Z)))).

Axiom Lsl_modulo_nth_low : forall (b:Uint16.t), forall (s:Uint16.t),
  forall (n:Z), ((0%Z <= (Uint16.to_int s))%Z /\
  ((Uint16.to_int s) < 16%Z)%Z) -> (((0%Z <= n)%Z /\ (n < 16%Z)%Z) ->
  (((n - (Uint16.to_int s))%Z < 0%Z)%Z -> ~ (nth (lsl_modulo b s) n))).

Axiom To_uint_lsr : forall (a:Uint16.t), forall (n:Uint16.t),
  (0%Z <= (Uint16.to_int n))%Z -> ((Uint16.to_int (lsr a
  n)) = (int.EuclideanDivision.div (Uint16.to_int a)
  (Powers_of_2.power2 (Uint16.to_int n)))).

Axiom To_uint_lsl_modulo : forall (a:Uint16.t), forall (n:Uint16.t),
  (0%Z <= (Uint16.to_int n))%Z -> ((Uint16.to_int (lsl_modulo a
  n)) = (int.EuclideanDivision.mod1 ((Uint16.to_int a) * (Powers_of_2.power2 (Uint16.to_int n)))%Z
  ((65535%Z - 0%Z)%Z + 1%Z)%Z)).

