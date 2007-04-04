

open Format
open Jc_env
open Jc_ast

type jc_decl =
  | JCfun_def of jc_type * string * (jc_type * string) list *
      tfun_spec * tstatement list

let string_of_native t =
  match t with
    | Tunit -> "unit"
    | Tinteger -> "integer"
    | Treal -> "real"
    | Tboolean -> "boolean"


let print_type fmt t =
  match t with
    | JCTnative n -> fprintf fmt "%s" (string_of_native n)
    | JCTlogic s -> fprintf fmt "%s" s
    | JCTrange ri -> fprintf fmt "%s" ri.jc_range_info_name
    | JCTpointer (s,_,_) -> fprintf fmt "%s" s.jc_struct_info_name

let print_decl fmt d =
  match d with
    | JCfun_def(ty,id,params,spec,body) ->
	fprintf fmt "%a %s() {}@." print_type ty id

let rec print_decls fmt d =
  match d with
    | [] -> ()
    | d::r -> print_decl fmt d; print_decls fmt r

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
