(* Interpretation of Ocaml programs to Jessie *)

open Ml_misc
open Ml_ocaml.Asttypes
open Ml_ocaml.Typedtree
open Ml_ocaml.Types
open Ml_ocaml.Path
open Ml_ocaml.Ident
open Jc_ast
open Jc_output
open Jc_env

let rec type_ env t = match t.desc with
  | Tconstr(Pident id, params, abbrev) ->
      begin match name id with
	| "unit" -> JCTnative Tunit
	| "bool" -> JCTnative Tboolean
	| "int" -> JCTnative Tinteger
	| "float" -> JCTnative Treal
	| s -> JCTlogic("ocaml_Tconstr_"^s)
      end
  | Tvar -> JCTlogic "ocaml_Tvar"
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

let constant = function
  | Const_int i -> JCTEconst(JCCinteger(string_of_int i))
  | Const_float s -> JCTEconst(JCCreal s)
  | _ -> not_implemented Ml_ocaml.Location.none "ml_interp.ml: constant"

let rec binary_op loc op = function
  | [ x; y ] -> JCTEbinary(x, op, y)
  | l -> locate_error loc "2 arguments required, %d found" (List.length l)

and expression env e =
  let binary_op = binary_op e.exp_loc in
  match e.exp_desc with
    | Texp_ident(Pident id, { val_kind = Val_reg }) ->
	JCTEvar(Ml_env.find_var (name id) env)
    | Texp_constant c -> constant c
(*  | Texp_let of rec_flag * (pattern * expression) list * expression
  | Texp_function of (pattern * expression) list * partial *)
    | Texp_apply(f, args) ->
	let args' = List.map
	  (function
	     | Some arg, Required ->
		 make_expr (expression env arg) (type_ env arg.exp_type)
	     | _ -> not_implemented e.exp_loc "apply with optional arguments")
	  args
	in
	begin match f.exp_desc with
	  | Texp_ident(Pident id, { val_kind = Val_reg }) ->
	      begin match name id with
		| ">=" -> binary_op Bge_int args'
		| x -> let fi = try
		    Ml_env.find_fun x env
		  with
		    | Not_found -> locate_error e.exp_loc
			"unknown function: %s" x
		  in
		  JCTEcall(fi, args')
	      end
	  | _ -> not_implemented e.exp_loc "unsupported application"
	end
(*  | Texp_match of expression * (pattern * expression) list * partial
  | Texp_try of expression * (pattern * expression) list
  | Texp_tuple of expression list
  | Texp_construct of constructor_description * expression list
  | Texp_variant of label * expression option
  | Texp_record of (label_description * expression) list * expression option
  | Texp_field of expression * label_description
  | Texp_setfield of expression * label_description * expression
  | Texp_array of expression list *)
    | Texp_ifthenelse(if_expr, then_expr, else_expr) ->
	let else', else_type = match else_expr with
	  | None -> JCTEconst JCCvoid, JCTnative Tunit
	  | Some expr -> expression env expr, type_ env expr.exp_type
	in
	JCTEif(
	  make_expr (expression env if_expr) (type_ env if_expr.exp_type),
	  make_expr (expression env then_expr) (type_ env if_expr.exp_type),
	  make_expr else' else_type)
(*  | Texp_sequence of expression * expression
  | Texp_while of expression * expression
  | Texp_for of
      Ident.t * expression * expression * direction_flag * expression
  | Texp_when of expression * expression
  | Texp_send of expression * meth
  | Texp_new of Path.t * class_declaration
  | Texp_instvar of Path.t * Path.t
  | Texp_setinstvar of Path.t * Path.t * expression
  | Texp_override of Path.t * (Path.t * expression) list
  | Texp_letmodule of Ident.t * module_expr * expression
  | Texp_assert of expression
  | Texp_assertfalse
  | Texp_lazy of expression
  | Texp_object of class_structure * class_signature * string list *)
    | _ -> not_implemented e.exp_loc "ml_interp.ml: expression"

let rec function_decl env e = match e.exp_desc with
  | Texp_function([ { pat_desc = Tpat_var pid;
		      pat_type = pty },
		    body ], _) ->
      let params, body' = function_decl env body in
      (pid, pty)::params, body'
  | _ -> [], e

let structure_item env = function
  | Tstr_value(_, [ { pat_desc = Tpat_var id },
		    ({ exp_desc = Texp_function _ } as expr) ]) ->
      let params, body = function_decl env expr in
      let return_type = type_ env body.exp_type in
      let new_env = List.fold_left
	(fun env (pid, pty) -> Ml_env.add_var (name pid) (type_ env pty) env)
	env
	params
      in
      let body' = {
	jc_tstatement_node = JCTSreturn(
	  return_type,
	  make_expr (expression new_env body) return_type);
	jc_tstatement_loc = Loc.dummy_position;
      } in
      let params' =
	List.map (fun (pid, _) -> Ml_env.find_var (name pid) new_env) params
      in
      JCfun_def(
	(* return type *)
	return_type,
	(* name *)
	name id,
	(* parameters *)
	params',
	(* pre and post-conditions *)
	{
	  jc_fun_requires = {
	    jc_assertion_node = JCAtrue;
	    jc_assertion_loc = Loc.dummy_position;
	    jc_assertion_label = "";
	  };
	  jc_fun_behavior = [];
	},
	(* body *)
	Some [ body' ]
      ), Ml_env.add_fun (name id) params' return_type new_env
  | x -> not_implemented Ml_ocaml.Location.none "ml_interp.ml.structure_item"

let structure env = List.map (structure_item env)

let rec structure env = function
  | [] -> [], env
  | si::tl ->
      let si', env' = structure_item env si in
      let sil, env'' = structure env' tl in
      si'::sil, env''

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)