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

let apply_op id args binary_op not_found = match (name id) with
  | ">=" -> binary_op Bge_int args
  |  x -> not_found x

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
	      apply_op id args' binary_op
		(fun x -> let fi = try
		    Ml_env.find_fun x env
		  with
		    | Ml_env.Not_found_str x -> locate_error e.exp_loc
			"unknown function: %s" x
		  in
		  JCTEcall(fi, args'))
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
	      apply_op id args' binary_op
		(fun x -> try
		   let li = Ml_env.find_logic_fun x env in
		   JCTapp(li, args')
		 with Ml_env.Not_found_str x ->
		   locate_error e.exp_loc "unknown logic function: %s" x)
	  | _ -> not_implemented e.exp_loc "unsupported application"
	end
(*    | Texp_match of expression * (pattern * expression) list * partial
    | Texp_try of expression * (pattern * expression) list
    | Texp_tuple of expression list
    | Texp_construct of constructor_description * expression list
    | Texp_variant of label * expression option
    | Texp_record of (label_description * expression) list * expression option*)
    | Texp_field(e, lbl) ->
	let te = term env e in
	let fi = Ml_env.find_field lbl.lbl_name env in
	JCTderef(make_term te (type_ env e.exp_type), fi)
(*    | Texp_setfield of expression * label_description * expression
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
	let new_env, vi =
	  Ml_env.add_var (name id) (type_ env eq_expr.exp_type) env
	in
	let in_ty = type_ new_env in_expr.exp_type in
	if is_unit in_ty then begin
	  (* no need for a temporary variable for the result *)
	  statement env eq_expr
	    (fun eq_res ->
	       make_statement_block [
		 make_var_decl vi (Some eq_res)
		   (statement new_env in_expr make_discard);
		 cont void;
	       ])
	end else begin
	  let in_tmp = new_var in_ty in
	  statement env eq_expr
	    (fun eq_res ->
	       make_var_decl in_tmp None
		 (make_statement_block [
		    make_var_decl vi (Some eq_res)
		      (statement new_env in_expr (make_affect in_tmp));
		    cont (make_expr (JCTEvar in_tmp) in_ty);
		  ]))
	end
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
		     (JCTnative Tunit))))
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
  log "    Record type %s:" (name id);
  log "      Looking for spec...";
  let spec =
    try
      Ml_env.find_type_spec id env
    with Ml_env.Not_found_str _ ->
      log "        Not found";
      {
	ts_type = Pident id;
	ts_invariants = [];
      }
  in
  let struct_name = name id in
  let struct_info = {
    jc_struct_info_name = struct_name;
    jc_struct_info_parent = None;
    jc_struct_info_root = struct_name;
    jc_struct_info_fields = []; (* set after *)
  } in
  log "      Fields...";
  let env, field_infos = list_fold_map
    (fun env (lbl, _, ty) ->
       Ml_env.add_field lbl (type_ env ty) struct_info env)
    env
    labels
  in
  struct_info.jc_struct_info_fields <- field_infos;
  log "      Invariants...";
  let env, invariants = list_fold_map
    (fun env i ->
       let inv_env, vi =
	 Ml_env.add_var
	   (name i.ti_argument)
	   (make_pointer_type struct_info)
	   env
       in
       let final_env, _ =
	 Ml_env.add_logic_fun (name i.ti_name) [ vi ] None env
       in
       final_env,
       (name i.ti_name, vi, make_assertion (assertion inv_env i.ti_body)))
    env
    spec.ts_invariants
  in
  Ml_env.add_struct struct_info env, (* replace existing structure *)
  JCstruct_def(struct_name, None, field_infos, invariants)

let variant_decl env (id, constrs) =
  log "    Variant type %s:" (name id);
(*  log "      Looking for spec...";
  let spec =
    try
      Ml_env.find_type_spec id env
    with Ml_env.Not_found_str _ ->
      log "        Not found";
      {
	ts_type = Pident id;
	ts_invariants = [];
      }
  in*)
  let struct_name = name id in
  let struct_info = {
    jc_struct_info_name = struct_name;
    jc_struct_info_parent = None;
    jc_struct_info_root = struct_name;
    jc_struct_info_fields = []; (* set after *)
  } in
  log "      Constructors...";
  let enum_info = {
    jc_enum_info_name = "variant_tag_"^struct_name;
    jc_enum_info_min = Num.num_of_int 0;
    jc_enum_info_max = Num.num_of_int (List.length constrs - 1);
  } in
  let env, tag_fi = Ml_env.add_field
    ("tag_"^struct_name)
    (JCTenum enum_info)
    struct_info env
  in
  let env, field_infos = list_fold_map
    (fun env (c, tyl) ->
       Ml_env.add_constructor c (List.map (type_ env) tyl) struct_info env)
    env
    constrs
  in
  let field_infos = tag_fi :: (List.flatten field_infos) in
  struct_info.jc_struct_info_fields <- field_infos;
  let invariants = [] in
  Ml_env.add_struct struct_info env, (* replace existing structure *)
  [ JCenum_type_def(
      enum_info.jc_enum_info_name,
      enum_info.jc_enum_info_min,
      enum_info.jc_enum_info_max);
    JCstruct_def(struct_name, None, field_infos, invariants) ]

let pre_declare_type name env =
  let si = {
    jc_struct_info_name = name; (* only this field is important *)
    jc_struct_info_parent = None;
    jc_struct_info_root = name;
    jc_struct_info_fields = [];
  } in
  Ml_env.add_struct si env

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
	  Ml_env.find_fun_spec id env
	with Ml_env.Not_found_str _ ->
	  log "        Not found";
	  {
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
  | Tstr_type l ->
      (* pre-declare types and split them between kinds *)
      let env, records, variants = List.fold_left
	(fun (env, records, variants) (id, td) ->
	   let name = name id in
	   match td.type_kind with
	     | Type_record(labels, _, _) ->
		 pre_declare_type name env,
		 (id, labels)::records,
		 variants
	     | Type_variant(constrs, _) ->
		 pre_declare_type name env,
		 records,
		 (id, constrs)::variants
	     | _ ->
		 not_implemented Ml_ocaml.Location.none
		   "unsupported type declaration kind for type %s" name)
	(env, [], [])
	l
      in
      let env, rd = (list_fold_map record_decl) env (List.rev records) in
      let env, vd = (list_fold_map variant_decl) env (List.rev variants) in
      [ JCrec_struct_defs(rd @ (List.flatten vd)) ], env
  | Tstr_function_spec _
  | Tstr_type_spec _ -> [], env
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
	 Ml_env.add_fun_spec id spec env
     | _ -> env)
  env

let add_type_specs env = List.fold_left
  (fun env -> function
     | Tstr_type_spec ({ ts_type = Pident id } as spec) ->
	 Ml_env.add_type_spec id spec env
     | _ -> env)
  env

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
