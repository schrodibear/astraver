
(* Why model for floating-point numbers
   Implements the file lib/why/floats.why *)

Require Export Reals.

Definition mode: Set.
Admitted.

Definition nearest_even : mode.
Admitted.

Definition to_zero : mode.
Admitted.

Definition up : mode.
Admitted.

Definition down : mode.
Admitted.

Definition nearest_away : mode.
Admitted.

Definition single: Set.
Admitted.

Definition add_single : mode -> single -> single -> single.
Admitted.

Definition sub_single : mode -> single -> single -> single.
Admitted.

Definition mul_single : mode -> single -> single -> single.
Admitted.

Definition div_single : mode -> single -> single -> single.
Admitted.

Definition neg_single : mode -> single -> single.
Admitted.

Definition abs_single : mode -> single -> single.
Admitted.

Definition sqrt_single : mode -> single -> single.
Admitted.

Definition s_to_r : single -> R.
Admitted.

Definition s_to_exact : single -> R.
Admitted.

Definition s_to_model : single -> R.
Admitted.

Definition r_to_s : mode -> R -> single.
Admitted.

Definition single_round_error : single -> R.
Admitted.

Definition single_total_error : single -> R.
Admitted.

Definition single_set_model : single -> R -> single.
Admitted.

Definition max_single : mode -> R.
Admitted.

Definition double: Set.
Admitted.

Definition add_double : mode -> double -> double -> double.
Admitted.

Definition sub_double : mode -> double -> double -> double.
Admitted.

Definition mul_double : mode -> double -> double -> double.
Admitted.

Definition div_double : mode -> double -> double -> double.
Admitted.

Definition neg_double : mode -> double -> double.
Admitted.

Definition abs_double : mode -> double -> double.
Admitted.

Definition sqrt_double : mode -> double -> double.
Admitted.

Definition d_to_r : double -> R.
Admitted.

Definition d_to_exact : double -> R.
Admitted.

Definition d_to_model : double -> R.
Admitted.

Definition r_to_d : mode -> R -> double.
Admitted.

Definition double_round_error : double -> R.
Admitted.

Definition double_total_error : double -> R.
Admitted.

Definition double_set_model : double -> R -> double.
Admitted.

Definition max_double : mode -> R.
Admitted.

Definition quad: Set.
Admitted.

Definition add_quad : mode -> quad -> quad -> quad.
Admitted.

Definition sub_quad : mode -> quad -> quad -> quad.
Admitted.

Definition mul_quad : mode -> quad -> quad -> quad.
Admitted.

Definition div_quad : mode -> quad -> quad -> quad.
Admitted.

Definition neg_quad : mode -> quad -> quad.
Admitted.

Definition abs_quad : mode -> quad -> quad.
Admitted.

Definition sqrt_quad : mode -> quad -> quad.
Admitted.

Definition q_to_r : quad -> R.
Admitted.

Definition q_to_exact : quad -> R.
Admitted.

Definition q_to_model : quad -> R.
Admitted.

Definition r_to_q : mode -> R -> quad.
Admitted.

Definition quad_round_error : quad -> R.
Admitted.

Definition quad_total_error : quad -> R.
Admitted.

Definition quad_set_model : quad -> R -> quad.
Admitted.

Definition max_quad : mode -> R.
Admitted.

Definition double_of_single : single -> double.
Admitted.

Definition single_of_double : mode -> double -> single.
Admitted.

Definition quad_of_single : single -> quad.
Admitted.

Definition single_of_quad : mode -> quad -> single.
Admitted.

Definition quad_of_double : double -> quad.
Admitted.

Definition double_of_quad : mode -> quad -> double.
Admitted.

