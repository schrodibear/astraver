(* Interpretation of Ocaml programs with simplified functions, to Jessie *)

open Ml_ocaml.Asttypes
open Ml_ast
open Jc_ast

(******************************************************************************)

exception Not_implemented of Ml_ocaml.Location.t * string

let not_implemented loc =
  Printf.ksprintf (fun s -> raise (Not_implemented(loc, s)))

(******************************************************************************)

let constant loc c = match c with
  | Const_int i -> JCTconst(JCCinteger(string_of_int i))
  | Const_float s -> JCTconst(JCCreal s)
  | Const_char _
  | Const_string _
  | Const_int32 _
  | Const_int64 _
  | Const_nativeint _ -> not_implemented loc "ml_interp.constant"

let rec expression e = match e.exp_desc with
  | Texp_ident(p, vd) ->
      not_implemented e.exp_loc "ml_interp.expression.Texp_ident"
  | Texp_constant c -> constant e.exp_loc c
  | _ -> not_implemented e.exp_loc "ml_interp.expression"

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
