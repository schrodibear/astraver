(* Interpretation of Ocaml types to Jessie *)

open Ml_misc
open Ml_ocaml.Asttypes
open Ml_ocaml.Typedtree
open Ml_ocaml.Types
open Ml_ocaml.Path
open Ml_ocaml.Ident
open Jc_ast
open Jc_output
open Jc_env

(* Return the Jessie structure associated with a given type. *)
(* Instanciate the structure if needed. *)
let type_struct_info env t = match t.desc with
  | Tconstr(Pident id, _, _) ->
      begin try
	Ml_env.find_struct (name id) env
      with Ml_env.Not_found_str s ->
	failwith ("ml_type.ml: type_struct_info ("^s^")")
      end
  | _ -> failwith "ml_type.ml: type_struct_info"

let rec type_ env t = match t.desc with
  | Tconstr(Pident id, params, abbrev) ->
      begin match name id with
	| "unit" -> JCTnative Tunit
	| "bool" -> JCTnative Tboolean
	| "int" -> JCTnative Tinteger
	| "float" -> JCTnative Treal
	| _ -> make_pointer_type(type_struct_info env t)
      end
  | Tvar -> JCTnative Tunit
  | Tarrow _ -> JCTlogic "ocaml_Tarrow"
  | Ttuple _ -> JCTlogic "ocaml_Ttuple"
  | Tconstr _ -> JCTlogic "ocaml_Tconstr"
  | Tobject _ -> JCTlogic "ocaml_Tobject"
  | Tfield _ -> JCTlogic "ocaml_Tfield"
  | Tnil -> JCTlogic "ocaml_Tnil"
  | Tlink ty -> type_ env ty
  | Tsubst _ -> JCTlogic "ocaml_Tsubst"
  | Tvariant _ -> JCTlogic "ocaml_Tvariant"
  | Tunivar -> JCTlogic "ocaml_Tunivar"
  | Tpoly _ -> JCTlogic "ocaml_Tpoly"

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
