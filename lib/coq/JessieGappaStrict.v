(* minimal set of definitions for using gappa library *)
(* formalization of the strict why model: why/lib/why/floats_strict.why *)

Require Export Reals.
Require Export Gappa_tactic.


Inductive float_format : Set :=  Single | Double.

Definition max_gen_float (f : float_format) :=
match f with 
| Single => (16777215*powerRZ 2 104)%R
            (* ((2-powerRZ 2 (-23))*powerRZ 2 127)%R *)
| Double => (9007199254740991 * powerRZ 2 971)%R
            (* (2 - 2 ^ (-52)) * 2 ^ 1023 = 2 ^ 1024 - 2 ^ 971 = (2^53 - 1) * 2^ 971 *)
end.


Definition min_gen_float (f:float_format) :=
 match f with 
  | Single => powerRZ 2 (-149)
  | Double => powerRZ 2 (-1074)
 end.


Inductive mode : Set := 
   nearest_even 
 | to_zero 
 | up 
 | down 
 | nearest_away.


Definition round_mode (m:mode) :=
  match m with 
  | nearest_even => roundNE
  | to_zero => roundZR
  | up => roundUP
  | down => roundDN
  | nearest_away => roundNA
  end.



(* generic floats*)

Definition gen_float := float2.

Parameter exact_value: gen_float -> R.
Parameter model_value: gen_float -> R.

Definition float_value x := float2R x.


Definition gen_round_error (x:gen_float) := 
               (Rabs ((exact_value x) - (float_value x))).
Definition gen_relative_error (x:gen_float) := 
               Rdiv (Rabs ((exact_value x) - (float_value x))) (exact_value x).
Definition gen_total_error (x:gen_float):= 
               (Rabs ((model_value x) - (float_value x))).
(*
Definition gen_set_model (x:gen_float) (r:R) :=
    model_value x = r.
*)

Definition round_float (f : float_format) (m : mode) (x:R) :=
match f with
| Single => gappa_rounding (rounding_float (round_mode m) 24 149) x
| Double => gappa_rounding (rounding_float (round_mode m) 53 1074) x
end.

Definition no_overflow (f : float_format) (m : mode) (x:R) :=
(Rabs (round_float f m x) <= max_gen_float f)%R.

Lemma overflow_dec : forall f m x, 
             no_overflow f m x \/ not (no_overflow f m x).
Proof.
intros; unfold no_overflow.
case (Rtotal_order (Rabs (round_float f m x)) (max_gen_float f));
auto with real; intros; elim H; auto with real.
Save.

Lemma round_of_zero: forall f m,
            (round_float f m 0 = 0)%R.
Proof.
intros; case f;case m;unfold round_float,round_mode;
admit. (*gappa succeeds but not with nearest_away *)
Save.

Lemma round_of_max_gen: forall f m,
            round_float f m (max_gen_float f) = max_gen_float f.
Proof.
intros; case f;case m;unfold round_float,round_mode, max_gen_float;
admit. (*gappa succeeds but not with nearest_away til today !! *)
Save.

Lemma round_of_opp_max_gen: forall f m,
            round_float f m (- max_gen_float f) = Ropp (max_gen_float f).
Proof.
intros; case f;case m;unfold round_float,round_mode, max_gen_float;
admit. (*gappa succeeds but not with nearest_away *)
Save.

Lemma round_of_min_gen: forall f m,
            round_float f m (min_gen_float f) = min_gen_float f.
Proof.
intros; case f;case m;unfold round_float,round_mode, min_gen_float;
admit. (*gappa succeeds but not with nearest_away *)
Save.

(*
Lemma round_of_float2: forall f m, forall x:float2, 
                                       round_float f m x = x.
*)

















(*
Lemma opp_of_float2: forall x:float2, exists y :float2, y = Ropp x.
*)

Lemma round_of_opp_min_gen: forall f m,
            round_float f m (- min_gen_float f) = Ropp (min_gen_float f).
Proof.
intros; case f;case m;unfold round_float,round_mode, min_gen_float;
admit. (*gappa succeeds but not with nearest_away *)
Save.


Lemma bounded_real_no_overflow : forall f m x, 
(Rabs x <= max_gen_float f)%R -> no_overflow f m x.
Proof.
intros f m x;case f; case m;
unfold no_overflow,round_float,round_mode,max_gen_float;intro;
admit. (*gappa succeeds but not with nearest_away til today !! *)
Save.


(*
(* powerRZ 2 (max_exp f) is the next gen_float after max_gen_float f *)
Definition max_exp (f:float_format) :=
match f with 
 | Single => 128%Z 
 | Double => 1024%Z  
end.


(* just for m <> nearest_even *)
Lemma bounded_real_overflow_pos : forall f m x,
(x > max_gen_float f)%R 
(* (max_gen_float f < x < powerRZ 2 (max_exp f))%R *) -> 
(m = up \/ m = nearest_away -> ~ no_overflow f m x) 
/\
(m = down \/ m = to_zero -> round_float f m x = max_gen_float f).
Proof.
Admitted.

(* just for m <> nearest_even *)
Lemma bounded_real_overflow_neg: forall f m x,
(x < - max_gen_float f)%R 
(* (- powerRZ 2 (max_exp f) < x < - max_gen_float f)%R *) -> 
(m = down \/ m = nearest_away -> ~ no_overflow f m x)
/\
(m = up \/ m = to_zero -> (round_float f m x = - max_gen_float f)%R).
Proof.
Admitted.

Lemma big_reals_overflow: forall f m x, 
(Rabs x >= powerRZ 2 (max_exp f))%R -> ~ no_overflow f m x.
Proof.
Admitted.
*)


Definition gen_float_of_real_logic (f : float_format) (m : mode) (x :R) :=
 match f with
  | Single => (rounding_float (round_mode m) 24 149) x
  | Double => (rounding_float (round_mode m) 53 1074) x
 end.

Axiom a1: forall f m x, no_overflow f m x ->
          float_value (gen_float_of_real_logic f m x) = round_float f m x.

Axiom a2: forall f m x,
                exact_value (gen_float_of_real_logic f m x) = x.

Axiom a3: forall f m x,
                 model_value (gen_float_of_real_logic f m x) = x.

Axiom a4: forall f m x,
          no_overflow f m x /\ (exists y, x = float_value y) -> 
          float_value (gen_float_of_real_logic f m x) = x.








