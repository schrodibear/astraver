(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)


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
     nearest_even <> to_zero and nearest_even <> up and nearest_even <> down 
     and nearest_even <> nearest_away and  to_zero <> up and to_zero <> down 
     and to_zero <> nearest_away and up <> down and up <> nearest_away and 
     down <> nearest_away

parameter current_rounding_mode : mode ref
@.@.";

  fprintf fmt "(* About the %s format *)
type %s@.@." t t;
  
  fprintf fmt "logic round_%s : mode, real -> real@.@." t;
  fprintf fmt "logic round_%s_logic : mode, real -> %s@.@." t t;

  fprintf fmt "logic %s_value : %s -> real
logic %s_exact : %s -> real
logic %s_model : %s -> real@.@." t t t t t t;

 
  fprintf fmt "function %s_round_error(x:%s) : real = 
	 abs_real(%s_value(x) - %s_exact(x))
function %s_total_error(x:%s) : real = 
	 abs_real(%s_value(x) - %s_model(x))@.@." t t t t t t t t;

fprintf fmt "parameter %s_set_model : x:%s ref -> y:real ->
  { } 
  unit writes x
  { %s_value(x) = %s_value(x@@)
    and %s_exact(x) = %s_exact(x@@)
    and %s_model(x) = y }@.@." t t t t t t t;

  fprintf fmt "function max_%s() : real = 0x1.%sp%d@.@." t (hex_of_precision (p-1)) (-p-e+2) ;

  fprintf fmt "predicate no_overflow_%s(m:mode,x:real) = 
	  abs_real(round_%s(m,x)) <= max_%s@.@." t t t;

  fprintf fmt "(* About rounding *)@.";
  fprintf fmt "axiom bounded_real_no_overflow_%s : forall m:mode. forall x:real. 
      abs_real(x) <= max_%s -> no_overflow_%s(m,x)@." t t t;
  fprintf fmt "axiom round_%s_down_le: forall x:real. 
      round_%s(down,x) <= x
axiom round_up_%s_ge: forall x:real. 
      round_%s(up,x) >= x
axiom round_down_%s_neg: forall x:real. 
     round_%s(down,-x) = -round_%s(up,x)
axiom round_up_%s_neg: forall x:real. 
     round_%s(up,-x) = -round_%s(down,x)
axiom round_%s_idempotent:
      forall m1:mode. forall m2:mode. forall x:real. 
      round_%s(m1,round_%s(m2,x)) = round_%s(m2,x)@.@." t t t t t t t t t t t t t t;

  fprintf fmt "(* Specification of operations (from the strict model) *)@.";
  fprintf fmt "predicate %s_of_real_post(m:mode,x:real,res:%s) =
    %s_value(res) = round_%s(m,x)
    and
    %s_exact(res) = x
    and
    %s_model(res) = x@.@." t t t t t t;

 fprintf fmt "predicate add_%s_post(m:mode,x:%s,y:%s,res:%s) =
    %s_value(res) = round_%s(m,%s_value(x) + %s_value(y))
    and 
    %s_exact(res) = %s_exact(x) + %s_exact(y)
    and 
    %s_model(res) = %s_model(x) + %s_model(y)@.@." t t t t t t t t t t t t t t;

 fprintf fmt "predicate sub_%s_post(m:mode,x:%s,y:%s,res:%s) =
    %s_value(res) = round_%s(m,%s_value(x) - %s_value(y))
    and 
    %s_exact(res) = %s_exact(x) - %s_exact(y)
    and 
    %s_model(res) = %s_model(x) - %s_model(y)@.@." t t t t t t t t t t t t t t;

 fprintf fmt "predicate mul_%s_post(m:mode,x:%s,y:%s,res:%s) =
    %s_value(res) = round_%s(m,%s_value(x) * %s_value(y))
    and 
    %s_exact(res) = %s_exact(x) * %s_exact(y)
    and 
    %s_model(res) = %s_model(x) * %s_model(y)@.@." t t t t t t t t t t t t t t;

 fprintf fmt "predicate div_%s_post(m:mode,x:%s,y:%s,res:%s) =
    %s_value(res) = round_%s(m,%s_value(x) / %s_value(y))
    and 
    %s_exact(res) = %s_exact(x) / %s_exact(y)
    and 
    %s_model(res) = %s_model(x) / %s_model(y)@.@." t t t t t t t t t t t t t t;

 fprintf fmt "predicate sqrt_%s_post(m:mode,x:%s,res:%s) =
    %s_value(res) = round_%s(m,sqrt_real(%s_value(x)))
    and 
    %s_exact(res) = sqrt_real(%s_exact(x))
    and 
    %s_model(res) = sqrt_real(%s_model(x))@.@."  t t t t t t t t t t;

 fprintf fmt "predicate neg_%s_post(x:%s,res:%s) =
    %s_value(res) = -%s_value(x)
    and 
    %s_exact(res) = -%s_exact(x)
    and 
    %s_model(res) = -%s_model(x)@.@."  t t t t t t t t t;

 fprintf fmt "predicate abs_%s_post(x:%s,res:%s) =
    %s_value(res) = abs_real(%s_value(x))
    and 
    %s_exact(res) = abs_real(%s_exact(x))
    and 
    %s_model(res) = abs_real(%s_model(x))@.@."  t t t t t t t t t;

();;

(* Strict  model *)

let output_strict_part fmt t _p _e =
  fprintf fmt "include \"%s_model.why\"@.@." t;
  fprintf fmt "(* Parameters for the strict model for %s format *)@.@." t;

  fprintf fmt "parameter %s_of_real : m:mode -> x:real ->
  { no_overflow_%s(m,x) }
  %s
  { %s_of_real_post(m,x,result) }@." t t t t;
  fprintf fmt "parameter %s_of_real_safe : m:mode -> x:real ->
  { }
  %s
  { no_overflow_%s(m,x) and
    %s_of_real_post(m,x,result) }@.@." t t t t;

  fprintf fmt "parameter add_%s : m:mode -> x:%s -> y:%s -> 
  { no_overflow_%s(m,%s_value(x) + %s_value(y)) }
  %s
  { add_%s_post(m,x,y,result) }@." t t t t t t t t;
  fprintf fmt "parameter add_%s_safe : m:mode -> x:%s -> y:%s -> 
  { }
  %s
  { no_overflow_%s(m,%s_value(x) + %s_value(y)) and
    add_%s_post(m,x,y,result) }@.@." t t t t t t t t;

  fprintf fmt "parameter sub_%s : m:mode -> x:%s -> y:%s -> 
  { no_overflow_%s(m,%s_value(x) - %s_value(y)) }
  %s
  { sub_%s_post(m,x,y,result) }@." t t t t t t t t;
  fprintf fmt "parameter sub_%s_safe : m:mode -> x:%s -> y:%s -> 
  { }
  %s
  { no_overflow_%s(m,%s_value(x) - %s_value(y)) and
    sub_%s_post(m,x,y,result) }@.@." t t t t t t t t;

  fprintf fmt "parameter mul_%s : m:mode -> x:%s -> y:%s -> 
  { no_overflow_%s(m,%s_value(x) * %s_value(y)) }
  %s
  { mul_%s_post(m,x,y,result) }@." t t t t t t t t;
  fprintf fmt "parameter mul_%s_safe : m:mode -> x:%s -> y:%s -> 
  { }
  %s
  { no_overflow_%s(m,%s_value(x) * %s_value(y)) and
    mul_%s_post(m,x,y,result) }@.@." t t t t t t t t;

  fprintf fmt "parameter div_%s : m:mode -> x:%s -> y:%s -> 
  { %s_value(y) <> 0.0 
    and
    no_overflow_%s(m,%s_value(x) / %s_value(y)) }
  %s
  { div_%s_post(m,x,y,result) }@." t t t t t t t t t;
  fprintf fmt "parameter div_%s_safe : m:mode -> x:%s -> y:%s -> 
  { }
  %s
  { %s_value(y) <> 0.0  and
    no_overflow_%s(m,%s_value(x) / %s_value(y)) and
    div_%s_post(m,x,y,result) }@.@." t t t t t t t t t;

  fprintf fmt "parameter sqrt_%s : m:mode -> x:%s -> 
  { %s_value(x) >= 0.0 }
  %s
  { sqrt_%s_post(m,x,result) }@." t t t t t;
  fprintf fmt "parameter sqrt_%s_safe : m:mode -> x:%s ->
  { }
  %s
  { %s_value(x) >= 0.0  and
    sqrt_%s_post(m,x,result) }@.@." t t t t t;

  fprintf fmt "parameter neg_%s : x:%s -> 
  { }
  %s
  { neg_%s_post(x,result) }@." t t t t;

  fprintf fmt "parameter abs_%s : x:%s -> 
  { }
  %s
  { abs_%s_post(x,result) }@." t t t t;

  fprintf fmt "(* Comparisons for the strict model for %s format *)@.@." t;
  fprintf fmt "parameter lt_%s : x:%s -> y:%s -> 
  {} bool { if result then %s_value(x) < %s_value(y) 
            else %s_value(x) >= %s_value(y) }@." t t t t t t t;
  fprintf fmt "parameter le_%s : x:%s -> y:%s -> 
  {} bool { if result then %s_value(x) <= %s_value(y) 
            else %s_value(x) > %s_value(y) }@." t t t t t t t;
  fprintf fmt "parameter gt_%s : x:%s -> y:%s -> 
  {} bool { if result then %s_value(x) > %s_value(y) 
            else %s_value(x) <= %s_value(y) }@." t t t t t t t;
  fprintf fmt "parameter ge_%s : x:%s -> y:%s -> 
  {} bool { if result then %s_value(x) >= %s_value(y) 
            else %s_value(x) < %s_value(y) }@." t t t t t t t;
  fprintf fmt "parameter eq_%s : x:%s -> y:%s -> 
  {} bool { if result then %s_value(x) = %s_value(y) 
            else %s_value(x) <> %s_value(y) }@." t t t t t t t;
  fprintf fmt "parameter neq_%s : x:%s -> y:%s -> 
  {} bool { if result then %s_value(x) <> %s_value(y) 
            else %s_value(x) = %s_value(y) }@.@." t t t t t t t;

fprintf fmt "(* Any %s *)
  parameter any_%s : { } %s { }" t t t;

();;

(* Coq  model *)

let output_coq_model fmt t p e =
  fprintf fmt "(* Coq model for float type '%s'
 * with precision = %d and min exponent = %d 
 *)@.@." t p e;

();;

(* main program *)

let type_name = Sys.argv.(1)

let precision = int_of_string Sys.argv.(2)

let exponent = int_of_string Sys.argv.(3)

let main = 
  let f = "lib/why/" ^ type_name ^ "_model.why" in
  let c = open_out f in
  output_common_part (formatter_of_out_channel c) type_name precision exponent;
  close_out c;

  let f = "lib/why/" ^ type_name ^ "_strict.why" in
  let c = open_out f in
  output_strict_part (formatter_of_out_channel c) type_name precision exponent;
  close_out c;

  let f = "lib/coq/" ^ type_name ^ "_model.v" in
  let c = open_out f in
  output_coq_model (formatter_of_out_channel c) type_name precision exponent;
  close_out c;




  
