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

let type_in_env env s =
  let si = Ml_env.find_struct s env in
  make_pointer_type si

let is_unit t = t = JCTnative Tunit

let rec type_ env t = match t.desc with
  | Tconstr(Pident id, params, abbrev) ->
      begin match name id with
	| "unit" -> JCTnative Tunit
	| "bool" -> JCTnative Tboolean
	| "int" -> JCTnative Tinteger
	| "float" -> JCTnative Treal
	| s ->
	    begin try
	      type_in_env env s
	    with Ml_env.Not_found_str _ ->
	      JCTlogic("ocaml_Tconstr_"^s)
	    end
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

let constant = function
  | Const_int i -> JCCinteger(string_of_int i)
  | Const_float s -> JCCreal s
  | _ -> not_implemented Ml_ocaml.Location.none "ml_interp.ml: constant"

let binary_op_expr loc op = function
  | [ x; y ] -> JCTEbinary(x, op, y)
  | l -> locate_error loc "2 arguments required, %d found" (List.length l)

let binary_op_term loc op = function
  | [ x; y ] -> JCTbinary(x, op, y)
  | l -> locate_error loc "2 arguments required, %d found" (List.length l)

exception Not_an_expression

let rec expression env e =
  let binary_op = binary_op_expr e.exp_loc in
  match e.exp_desc with
    | Texp_ident(Pident id, { val_kind = Val_reg }) ->
	JCTEvar(Ml_env.find_var (name id) env)
    | Texp_constant c -> JCTEconst(constant c)
    | Texp_let((Nonrecursive | Default),
	       [ { pat_desc = Tpat_var id }, eq_expr ], in_expr) ->
	let new_env, vi =
	  Ml_env.add_var (name id) (type_ env eq_expr.exp_type) env
	in
	JCTElet(
	  vi,
	  make_expr (expression env eq_expr) (type_ env eq_expr.exp_type),
	  make_expr (expression new_env in_expr) (type_ env in_expr.exp_type))
    | Texp_let(Recursive, _, _) ->
	not_implemented e.exp_loc "recursive let"
    | Texp_function _ ->
	locate_error e.exp_loc
	  "ml_interp.ml, in expression: the AST is not defunctionalized"
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
		    | Ml_env.Not_found_str x -> locate_error e.exp_loc
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
    | Texp_variant of label * expression option *)
    | Texp_record(lbls, None) ->
	let si = match lbls with
	  | [] ->
	      locate_error e.exp_loc "empty record"
	  | (lbl, _)::_ ->
	      (Ml_env.find_field lbl.lbl_name env).jc_field_info_struct
	in
	let lbls = List.map
	  (fun (ld, e) ->
	     ld.lbl_name, make_expr (expression env e) (type_ env e.exp_type))
	  lbls
	in
	let tmp_ty = make_pointer_type si in
	let tmp_var = new_var tmp_ty in
	let tmp_expr = make_expr (JCTEvar tmp_var) tmp_ty in
	let assigns = List.map
	  (fun (lbl, e) ->
	     make_expr
	       (JCTEassign_heap(tmp_expr, Ml_env.find_field lbl env, e))
	       e.jc_texpr_type)
	  lbls
	in
	JCTElet(
	  tmp_var,
	  make_expr (JCTEalloc(expr_of_int 1, si)) tmp_ty,
	  expr_seq_to_let assigns (make_expr (JCTEvar tmp_var) tmp_ty)
	)
    | Texp_record(_, Some _) ->
	not_implemented e.exp_loc "record with"
    | Texp_field(x, lbl) ->
	let tx = make_expr (expression env x) (type_ env x.exp_type) in
	let fi = Ml_env.find_field lbl.lbl_name env in
	JCTEderef(tx, fi)
    | Texp_setfield(x, lbl, v) ->
	let tx = make_expr (expression env x) (type_ env x.exp_type) in
	let tv = make_expr (expression env v) (type_ env v.exp_type) in
	let fi = Ml_env.find_field lbl.lbl_name env in
	JCTEassign_heap(tx, fi, tv)
(*  | Texp_array of expression list *)
    | Texp_ifthenelse(if_expr, then_expr, else_expr) ->
	let else', else_type = match else_expr with
	  | None -> JCTEconst JCCvoid, JCTnative Tunit
	  | Some expr -> expression env expr, type_ env expr.exp_type
	in
	JCTEif(
	  make_expr (expression env if_expr) (type_ env if_expr.exp_type),
	make_expr (expression env then_expr) (type_ env if_expr.exp_type),
	  make_expr else' else_type)
(*  | Texp_sequence of expression * expression *)
    | Texp_while _
    | Texp_for _ -> raise Not_an_expression
(*  | Texp_when of expression * expression
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

let rec term env e =
  let binary_op = binary_op_term e.exp_loc in
  match e.exp_desc with
    | Texp_ident(Pident id, { val_kind = Val_reg }) ->
	JCTvar(Ml_env.find_var (name id) env)
    | Texp_constant c -> JCTconst(constant c)
(*    | Texp_let of rec_flag * (pattern * expression) list * expression
    | Texp_function of (pattern * expression) list * partial*)
    | Texp_apply(f, args) ->
	let args' = List.map
	  (function
	     | Some arg, Required ->
		 make_term (term env arg) (type_ env arg.exp_type)
	     | _ -> not_implemented e.exp_loc "apply with optional arguments")
	  args
	in
	begin match f.exp_desc with
	  | Texp_ident(Pident id, { val_kind = Val_reg }) ->
	      begin match name id with
		| ">=" -> binary_op Bge_int args'
		| _ -> not_implemented e.exp_loc "unsupported application"
	      end
	  | _ -> not_implemented e.exp_loc "unsupported application"
	end
(*    | Texp_match of expression * (pattern * expression) list * partial
    | Texp_try of expression * (pattern * expression) list
    | Texp_tuple of expression list
    | Texp_construct of constructor_description * expression list
    | Texp_variant of label * expression option
    | Texp_record of (label_description * expression) list * expression option
    | Texp_field of expression * label_description
    | Texp_setfield of expression * label_description * expression
    | Texp_array of expression list
    | Texp_ifthenelse(if_expr, then_expr, else_expr) ->
    | Texp_sequence of expression * expression
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
    | Texp_result ->
	JCTvar (Jc_pervasives.var (type_ env e.exp_type) "\\result")
    | _ -> not_implemented e.exp_loc "ml_interp.ml: term"

let rec assertion env e =
  match e.exp_desc with
    | Texp_ident _ ->
	JCAbool_term(make_term (term env e) (type_ env e.exp_type))
(*    | Texp_constant c
    | Texp_let of rec_flag * (pattern * expression) list * expression
    | Texp_function of (pattern * expression) list * partial*)
    | Texp_apply(f, args) ->
	let args_assertion () = List.map
	  (function
	     | Some arg, Required ->
		 make_assertion (assertion env arg)
	     | _ -> not_implemented e.exp_loc "apply with optional arguments")
	  args
	in
	begin match f.exp_desc with
	  | Texp_ident(Pident id, { val_kind = Val_reg }) ->
	      begin match name id with
		| "&&" -> (make_and_list (args_assertion ())).jc_assertion_node
		| _ ->
		    JCAbool_term(make_term (term env e) (type_ env e.exp_type))
	      end
	  | _ -> not_implemented e.exp_loc "unsupported application"
	end
(*    | Texp_match of expression * (pattern * expression) list * partial
    | Texp_try of expression * (pattern * expression) list
    | Texp_tuple of expression list
    | Texp_construct of constructor_description * expression list
    | Texp_variant of label * expression option
    | Texp_record of (label_description * expression) list * expression option
    | Texp_field of expression * label_description
    | Texp_setfield of expression * label_description * expression
    | Texp_array of expression list
    | Texp_ifthenelse(if_expr, then_expr, else_expr) ->
    | Texp_sequence of expression * expression
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
    | Texp_result ->
	assert false (* impossible *)
    | _ -> not_implemented e.exp_loc "ml_interp.ml: assertion"

let rec statement env e cont =
  match e.exp_desc with
    | Texp_ident _
    | Texp_constant _ ->
	cont (make_expr (expression env e) (type_ env e.exp_type))
    | Texp_let((Nonrecursive | Default),
	       [ { pat_desc = Tpat_var id }, eq_expr ], in_expr) ->
	let ty = type_ env eq_expr.exp_type in
	let new_env, vi =
	  Ml_env.add_var (name id) ty env
	in
	let tmp = new_var ty in
	statement env eq_expr
	  (fun eq_res ->
	     make_var_decl tmp None
	       (make_statement_block [
		  make_var_decl vi (Some eq_res)
		    (statement new_env in_expr (make_affect tmp));
		  cont (make_expr (JCTEvar tmp) ty);
	       ]))
    | Texp_let(Recursive, _, _) ->
	not_implemented e.exp_loc "recursive let"
(*    | Texp_function of (pattern * expression) list * partial
    | Texp_apply(f, args) ->
    | Texp_match of expression * (pattern * expression) list * partial
    | Texp_try of expression * (pattern * expression) list
    | Texp_tuple of expression list
    | Texp_construct of constructor_description * expression list
    | Texp_variant of label * expression option*)
    | Texp_record(lbls, None) ->
	let si = match lbls with
	  | [] ->
	      locate_error e.exp_loc "empty record"
	  | (lbl, _)::_ ->
	      (Ml_env.find_field lbl.lbl_name env).jc_field_info_struct
	in
	let tmp_ty = make_pointer_type si in
	let tmp_var = new_var tmp_ty in
	let tmp_expr = make_expr (JCTEvar tmp_var) tmp_ty in
	let tmp_init = Some (make_expr (JCTEalloc(expr_of_int 1, si)) tmp_ty) in
	let affect fi v =
	  make_statement
	    (JCTSexpr(make_expr (JCTEassign_heap(tmp_expr, fi, v))
			fi.jc_field_info_type))
	in
	let affects = List.map
	  (fun (ld, e) ->
	     let fi = Ml_env.find_field ld.lbl_name env in
	     statement env e (affect fi))
	  lbls
	in
	make_var_decl tmp_var tmp_init
	  (make_statement_block (affects @ [ cont tmp_expr ]))
    | Texp_record(_, Some _) ->
	not_implemented e.exp_loc "record with"
    | Texp_field(e, lbl) ->
	let fi = Ml_env.find_field lbl.lbl_name env in
	statement env e
	  (fun res -> cont
	     (make_expr (JCTEderef(res, fi))
		fi.jc_field_info_type))
    | Texp_setfield(e, lbl, v) ->
	let fi = Ml_env.find_field lbl.lbl_name env in
	statement env e
	  (fun res ->
	     statement env v
	       (fun res2 -> cont
		  (make_expr (JCTEassign_heap(res, fi, res2))
		     fi.jc_field_info_type)))
(*    | Texp_array of expression list*)
    | Texp_ifthenelse(if_expr, then_expr, else_expr) ->
	let ty = type_ env then_expr.exp_type in
	if is_unit ty then begin
	  (* no temporary variable for the result, as it is discarded *)
	  statement env if_expr
	    (fun if_res ->
	       let if_statement =
		 JCTSif(
		   if_res,
		   statement env then_expr cont,
		   match else_expr with
		     | None -> make_statement (JCTSblock [])
		     | Some e -> statement env e cont)
	       in
	       make_statement if_statement)
	end else begin
	  let tmp = new_var ty in
	  statement env if_expr
	    (fun if_res ->
	       let if_statement =
		 JCTSif(
		   if_res,
		   statement env then_expr (make_affect tmp),
		   match else_expr with
		     | None -> make_statement (JCTSblock [])
		     | Some e -> statement env e (make_affect tmp))
	       in
	       make_var_decl tmp None
		 (make_statement_block [
		    make_statement if_statement;
		    cont (make_expr (JCTEvar tmp) ty);
		  ]))
	end
    | Texp_sequence(e1, e2) ->
	make_statement_block [
	  statement env e1 make_discard;
	  statement env e2 cont;
	]
(*    | Texp_while of expression * expression
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
    | Texp_result ->
	assert false (* impossible *)
    | _ -> not_implemented e.exp_loc "ml_interp.ml: statement"

let behavior env b =
  log "        Behavior %s..." b.b_name;
  Loc.dummy_position,
  b.b_name,
  { 
    jc_behavior_throws = None;
    jc_behavior_assumes = None;
    jc_behavior_assigns = None;
    jc_behavior_ensures = make_assertion(assertion env b.b_ensures);
  }

let record_decl env (id, labels) =
  let struct_name = name id in
  let struct_info = {
    jc_struct_info_name = struct_name;
    jc_struct_info_parent = None;
    jc_struct_info_root = struct_name;
    jc_struct_info_fields = []; (* set after *)
  } in
  let env, field_infos = list_fold_map
    (fun env (lbl, _, ty) ->
       Ml_env.add_field lbl (type_ env ty) struct_info env)
    env
    labels
  in
  struct_info.jc_struct_info_fields <- field_infos;
  let invariants = [] in
  JCstruct_def(struct_name, None, field_infos, invariants),
  Ml_env.add_struct struct_info env

let record_decls env l =
  let decls, env = List.fold_left
    (fun (acc, env) r ->
       let d, env = record_decl env r in
       d::acc, env)
    ([], env)
    l
  in [ JCrec_struct_defs decls ], env

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
      log "    Function %s:" (name id);
      let params, body = function_decl env expr in
      log "      Looking for spec...";
      let spec =
	try
	  Ml_env.find_spec id env
	with Ml_env.Not_found_str _ -> {
	  fs_function = Pident id;
	  fs_arguments = []; (* unused *)
	  fs_requires = None;
	  fs_behaviors = [];
	}
      in
      log "      Return type...";
      let return_type = type_ env body.exp_type in
      log "      Building environment...";
      let new_env, params' = list_fold_map
	(fun env (pid, pty) -> Ml_env.add_var (name pid) (type_ env pty) env)
	env
	params
      in
      log "      Body...";
      let body' = statement new_env body
	(if is_unit return_type then make_discard else make_return)
      in
      log "      Requires...";
      let requires = match spec.fs_requires with
	| None -> JCAtrue
	| Some x -> assertion new_env x
      in
      log "      Behaviors...";
      let behaviors = List.map (behavior new_env) spec.fs_behaviors in
      log "      Finalizing...";
      let jc_spec = {
	jc_fun_requires = {
	  jc_assertion_node = requires;
	  jc_assertion_loc = Loc.dummy_position;
	  jc_assertion_label = "";
	};
	jc_fun_behavior = behaviors;
      } in
      let jc_fun_def =
	JCfun_def(
	  return_type,
	  name id,
	  params',
	  jc_spec,
	  Some [ body' ]
	)
      in
      [ jc_fun_def ], Ml_env.add_fun (name id) params' return_type new_env
  | Tstr_function_spec _ -> [], env
  | Tstr_type l ->
      let records = List.map
	(fun (id, td) ->
	   match td.type_kind with
	     | Type_record(labels, _, _) -> Some(id, labels)
	     | _ -> None)
	l
      in
      let records = list_filter_option records in
      record_decls env records
  | x -> not_implemented Ml_ocaml.Location.none "ml_interp.ml.structure_item"

let rec structure env = function
  | [] -> [], env
  | si::tl ->
      let jc_items, new_env = structure_item env si in
      let jc_rem_items, final_env = structure new_env tl in
      jc_items @ jc_rem_items, final_env

let add_structure_specs env = List.fold_left
  (fun env -> function
     | Tstr_function_spec ({ fs_function = Pident id } as spec) ->
	 Ml_env.add_spec id spec env
     | _ -> env)
  env

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
