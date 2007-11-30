(* Interpretation of Ocaml programs with simplified functions, to Jessie *)

open Ml_misc
open Ml_ocaml.Asttypes
open Ml_ast
open Jc_ast

let constant loc c = match c with
  | Const_int i -> JCTconst(JCCinteger(string_of_int i))
  | Const_float s -> JCTconst(JCCreal s)
  | Const_char _
  | Const_string _
  | Const_int32 _
  | Const_int64 _
  | Const_nativeint _ -> not_implemented loc "ml_interp.constant"

let rec expression e = match e.jexp_desc with
  | JTexp_ident(p, vd) ->
      not_implemented e.jexp_loc "ml_interp.expression.Texp_ident"
  | JTexp_constant c -> constant e.jexp_loc c
  | _ -> not_implemented e.jexp_loc "ml_interp.expression"

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
