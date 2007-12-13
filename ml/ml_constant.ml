(* Interpretation of Ocaml constants to Jessie *)

open Ml_misc
open Ml_ocaml.Asttypes
open Jc_ast
open Jc_env

let constant = function
  | Const_int i -> JCCinteger(string_of_int i)
  | Const_float s -> JCCreal s
  | _ -> not_implemented Ml_ocaml.Location.none "ml_constant.ml: constant"

let constant_type = function
  | Const_int _ -> JCTnative Tinteger
  | Const_float _ -> JCTnative Treal
  | _ -> not_implemented Ml_ocaml.Location.none "ml_constant.ml: constant_type"

let constant_term c =
  make_term (JCTconst (constant c)) (constant_type c)
