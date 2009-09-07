

open Format


(*

  t : name of the float type
  p : precision
  e : minimal exponent (2^e is the smallest subnormal number

eg:

  t = "double", p = 53, e = -1074

  t = "single", p = 24, e = -149

*)

let rec hex_of_precision p =
  match p with
    | 0 -> ""
    | 1 -> "8"
    | 2 -> "C"
    | 3 -> "E"
    | _ -> "F" ^ hex_of_precision (p-4)

let output_common_part fmt t p e =

  fprintf fmt "include \"real.why\"@.@.";

  fprintf fmt "(* the different rounding modes *)

type mode 

logic nearest_even, to_zero, up, down, nearest_away : mode

axiom no_other_mode : forall m:mode. 
      m = nearest_even or m = to_zero or m = up or m = down or m = nearest_away
axiom mode_distinct : 
      nearest_even <> to_zero and nearest_even <> up and nearest_even <> down and 
      nearest_even <> nearest_away and  to_zero <> up and to_zero <> down and 
      to_zero <> nearest_away and up <> down and up <> nearest_away and 
      down <> nearest_away

parameter current_rounding_mode : mode ref
@.@.";

  fprintf fmt "type %s@.@." t;
  
  fprintf fmt "logic round_%s : mode, real -> real@.@." t;

  fprintf fmt "logic %s_value : %s -> real
logic %s_exact : %s -> real
logic %s_model : %s -> real@.@." t t t t t t;

  fprintf fmt "function max_%s() : real = 0x1.%sp%d@.@." t (hex_of_precision (p-1)) (-p-e+2) ;

  fprintf fmt "predicate no_overflow_%s(m:mode,x:real) = 
	  abs_real(round_%s(m,x)) <= max_%s@.@." t t t




(* Coq  model *)

let output_coq_model fmt t p e =
  fprintf fmt "(* Coq model for float type '%s'
 * with precision = %d and min exponent = %d 
 *)@.@." t p e

(* main program *)

let type_name = Sys.argv.(1)

let precision = int_of_string Sys.argv.(2)

let exponent = int_of_string Sys.argv.(3)

let main = 
  let f = "lib/why/" ^ type_name ^ "_model.why" in
  let c = open_out f in
  output_common_part (formatter_of_out_channel c) type_name precision exponent;
  close_out c;

  let f = "lib/coq/" ^ type_name ^ "_model.v" in
  let c = open_out f in
  output_coq_model (formatter_of_out_channel c) type_name precision exponent;
  close_out c;




  
