(* Why model for floating-point numbers
   Implements the file lib/why/floats_strict.why *)

Require Export WhyFloats.

(* Double and Single precision: axioms *)

Axiom double_le_strict: forall (s:double), 
   (Rabs (double_value s) <= max_double)%R.

Axiom single_le_strict: forall (s:single), 
   (Rabs (single_value s) <= max_single)%R.

(* Various Why predicates. Only definitions are left. *)

(*Why predicate*) Definition single_of_real_post  (m:mode) (x:R) (res:single)
  := (eq (single_value res) (round_single m x)) /\
     (eq (single_exact res) x) /\ (eq (single_model res) x).

(*Why predicate*) Definition add_single_post  (m:mode) (x:single) (y:single) (res:single)
  := (eq (single_value res) (round_single
                             m (Rplus (single_value x) (single_value y)))) /\
     (eq (single_exact res) (Rplus (single_exact x) (single_exact y))) /\
     (eq (single_model res) (Rplus (single_model x) (single_model y))).

(*Why predicate*) Definition sub_single_post  (m:mode) (x:single) (y:single) (res:single)
  := (eq (single_value res) (round_single
                             m (Rminus (single_value x) (single_value y)))) /\
     (eq (single_exact res) (Rminus (single_exact x) (single_exact y))) /\
     (eq (single_model res) (Rminus (single_model x) (single_model y))).

(*Why predicate*) Definition mul_single_post  (m:mode) (x:single) (y:single) (res:single)
  := (eq (single_value res) (round_single
                             m (Rmult (single_value x) (single_value y)))) /\
     (eq (single_exact res) (Rmult (single_exact x) (single_exact y))) /\
     (eq (single_model res) (Rmult (single_model x) (single_model y))).

(*Why predicate*) Definition div_single_post  (m:mode) (x:single) (y:single) (res:single)
  := (eq (single_value res) (round_single
                             m (Rdiv (single_value x) (single_value y)))) /\
     (eq (single_exact res) (Rdiv (single_exact x) (single_exact y))) /\
     (eq (single_model res) (Rdiv (single_model x) (single_model y))).

(*Why predicate*) Definition sqrt_single_post  (m:mode) (x:single) (res:single)
  := (eq (single_value res) (round_single m (sqrt (single_value x)))) /\
     (eq (single_exact res) (sqrt (single_exact x))) /\
     (eq (single_model res) (sqrt (single_model x))).

(*Why predicate*) Definition neg_single_post  (x:single) (res:single)
  := (eq (single_value res) (Ropp (single_value x))) /\
     (eq (single_exact res) (Ropp (single_exact x))) /\
     (eq (single_model res) (Ropp (single_model x))).

(*Why predicate*) Definition abs_single_post  (x:single) (res:single)
  := (eq (single_value res) (Rabs (single_value x))) /\
     (eq (single_exact res) (Rabs (single_exact x))) /\
     (eq (single_model res) (Rabs (single_model x))).

(*Why predicate*) Definition double_of_real_post  (m:mode) (x:R) (res:double)
  := (eq (double_value res) (round_double m x)) /\
     (eq (double_exact res) x) /\ (eq (double_model res) x).

(*Why predicate*) Definition add_double_post  (m:mode) (x:double) (y:double) (res:double)
  := (eq (double_value res) (round_double
                             m (Rplus (double_value x) (double_value y)))) /\
     (eq (double_exact res) (Rplus (double_exact x) (double_exact y))) /\
     (eq (double_model res) (Rplus (double_model x) (double_model y))).

(*Why predicate*) Definition sub_double_post  (m:mode) (x:double) (y:double) (res:double)
  := (eq (double_value res) (round_double
                             m (Rminus (double_value x) (double_value y)))) /\
     (eq (double_exact res) (Rminus (double_exact x) (double_exact y))) /\
     (eq (double_model res) (Rminus (double_model x) (double_model y))).

(*Why predicate*) Definition mul_double_post  (m:mode) (x:double) (y:double) (res:double)
  := (eq (double_value res) (round_double
                             m (Rmult (double_value x) (double_value y)))) /\
     (eq (double_exact res) (Rmult (double_exact x) (double_exact y))) /\
     (eq (double_model res) (Rmult (double_model x) (double_model y))).

(*Why predicate*) Definition div_double_post  (m:mode) (x:double) (y:double) (res:double)
  := (eq (double_value res) (round_double
                             m (Rdiv (double_value x) (double_value y)))) /\
     (eq (double_exact res) (Rdiv (double_exact x) (double_exact y))) /\
     (eq (double_model res) (Rdiv (double_model x) (double_model y))).

(*Why predicate*) Definition sqrt_double_post  (m:mode) (x:double) (res:double)
  := (eq (double_value res) (round_double m (sqrt (double_value x)))) /\
     (eq (double_exact res) (sqrt (double_exact x))) /\
     (eq (double_model res) (sqrt (double_model x))).

(*Why predicate*) Definition neg_double_post  (x:double) (res:double)
  := (eq (double_value res) (Ropp (double_value x))) /\
     (eq (double_exact res) (Ropp (double_exact x))) /\
     (eq (double_model res) (Ropp (double_model x))).

(*Why predicate*) Definition abs_double_post  (x:double) (res:double)
  := (eq (double_value res) (Rabs (double_value x))) /\
     (eq (double_exact res) (Rabs (double_exact x))) /\
     (eq (double_model res) (Rabs (double_model x))).

