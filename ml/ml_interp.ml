(* Interpretation of Ocaml programs to Jessie *)

open Jc_ast
open Jc_output
open Jc_env
open Jc_fenv
open Ml_misc
open Ml_pattern
open Ml_constant
open Ml_ocaml.Asttypes
open Ml_ocaml.Typedtree
open Ml_ocaml.Types
open Ml_ocaml.Path
open Ml_ocaml.Ident
open Ml_type

let binary_op_of_string = function
  | ">=" -> Bge_int
  | ">" -> Bgt_int
  | "<=" -> Ble_int
  | "<" -> Blt_int
  | "=" -> Beq_int
  | "<>" -> Bneq_int
  | "*" -> Bmul_int
  | "/" -> Bdiv_int
  | "+" -> Badd_int
  | "-" -> Bsub_int
  | _ -> raise Not_found

let binary_op_type = function
  | Bge_int
  | Bgt_int
  | Ble_int
  | Blt_int
  | Beq_int
  | Bneq_int -> JCTnative Tboolean
  | Bmul_int
  | Bdiv_int
  | Badd_int
  | Bsub_int -> JCTnative Tinteger
  | _ -> failwith "binary_op_type"

let binary_op_expr loc op = function
  | [ x; y ] -> JCTEbinary(x, op, y)
  | l -> locate_error loc "2 arguments required, %d found" (List.length l)

let binary_op_term loc op = function
  | [ x; y ] -> JCTbinary(x, op, y)
  | l -> locate_error loc "2 arguments required, %d found" (List.length l)

let apply_op id args binary_op not_found =
  try
    binary_op (binary_op_of_string (name id)) args
  with Not_found ->
    not_found (name id)

let apply_op_expr id args binary_op not_found =
  try
    let op = binary_op_of_string (name id) in
    make_expr (binary_op op args) (binary_op_type op)
  with Not_found ->
    not_found (name id)

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
	  Ml_env.add_var (name id) (make eq_expr.exp_type) env
	in
	JCTElet(
	  vi,
	  make_expr (expression env eq_expr) (make eq_expr.exp_type),
	  make_expr (expression new_env in_expr) (make in_expr.exp_type))
    | Texp_let(Recursive, _, _) ->
	not_implemented e.exp_loc "recursive let"
    | Texp_function _ ->
	locate_error e.exp_loc
	  "ml_interp.ml, in expression: the AST is not defunctionalized"
    | Texp_apply(f, args) ->
	let args' = List.map
	  (function
	     | Some arg, Required ->
		 make_expr (expression env arg) (make arg.exp_type)
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
	  | _ -> not_implemented e.exp_loc "unsupported application (expression)"
	end
    | Texp_match(e, pel, partial) ->
	let e = PatExpression.pattern_expr_list
	  env
	  (make_expr (expression env e) (make e.exp_type))
	  (List.map
	     (fun (pat, expr) ->
		pat,
		fun env2 ->
		  make_expr (expression env2 expr) (make expr.exp_type))
	     pel)
	  (match partial with
	     | Partial ->
		 not_implemented e.exp_loc
		   "partial pattern-matching (expression)"
	     | Total ->
		 None)
	in e.jc_texpr_node
(*    | Texp_try of expression * (pattern * expression) list
    | Texp_tuple of expression list*)
    | Texp_construct(cd, el) ->
	let ci = constructor e.exp_type cd in
	make_let_alloc_tmp ci.ml_ci_structure
	  (fun vi ve ->
	     make_seq_expr
	       ((make_affect_field_expr ve ci.ml_ci_tag_field
		   (expr_of_int ci.ml_ci_tag))::
		   (List.map2
		      (make_affect_field_expr ve)
		      ci.ml_ci_arguments
		      (List.map
			 (fun e ->
			    make_expr (expression env e) (make e.exp_type))
			 el)))
	       ve)
(*    | Texp_variant of label * expression option *)
    | Texp_record(lbls, None) ->
	not_implemented e.exp_loc "TO REDO: ml_interp.ml: expression: records (make_let_tmp, label, ...)";
	(*let si = match lbls with
	  | [] ->
	      locate_error e.exp_loc "empty record"
	  | (lbl, _)::_ ->
	      (label e.exp_type lbl).ml_li_structure
	in
	let lbls = List.map
	  (fun (ld, e) ->
	     label ld, make_expr (expression env e) (make e.exp_type))
	  lbls
	in
	let tmp_ty = make_pointer_type si in
	let tmp_var = new_var tmp_ty in
	let tmp_expr = make_expr (JCTEvar tmp_var) tmp_ty in
	let assigns = List.map
	  (fun (lbl, e) ->
	     make_expr
	       (JCTEassign_heap(tmp_expr, lbl.ml_li_field, e))
	       e.jc_texpr_type)
	  lbls
	in
	JCTElet(
	  tmp_var,
	  make_expr (JCTEalloc(expr_of_int 1, si)) tmp_ty,
	  expr_seq_to_let assigns (make_expr (JCTEvar tmp_var) tmp_ty)
	)*)
    | Texp_record(_, Some _) ->
	not_implemented e.exp_loc "record with"
    | Texp_field(x, lbl) ->
	let tx = make_expr (expression env x) (make x.exp_type) in
	let fi = (label x.exp_type lbl).ml_li_field in
	JCTEderef(tx, fi)
    | Texp_setfield(x, lbl, v) ->
	let tx = make_expr (expression env x) (make x.exp_type) in
	let tv = make_expr (expression env v) (make v.exp_type) in
	let fi = (label x.exp_type lbl).ml_li_field in
	JCTEassign_heap(tx, fi, tv)
(*  | Texp_array of expression list *)
    | Texp_ifthenelse(if_expr, then_expr, else_expr) ->
	let else', else_type = match else_expr with
	  | None -> JCTEconst JCCvoid, JCTnative Tunit
	  | Some expr -> expression env expr, make expr.exp_type
	in
	JCTEif(
	  make_expr (expression env if_expr) (make if_expr.exp_type),
	make_expr (expression env then_expr) (make if_expr.exp_type),
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
    | Texp_result
    | Texp_old _ ->
	assert false (* impossible *)
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
		 make_term (term env arg) (make arg.exp_type)
	     | _ -> not_implemented e.exp_loc "apply with optional arguments")
	  args
	in
	begin match f.exp_desc with
	  | Texp_ident(Pident id, { val_kind = Val_reg }) ->
	      apply_op id args' binary_op
		(fun x -> try
		   let li = Ml_env.find_logic_fun x env in
		   make_app_term_node li args'
		 with Ml_env.Not_found_str x ->
		   locate_error e.exp_loc "unknown logic function: %s" x)
	  | _ -> not_implemented e.exp_loc "unsupported application (term)"
	end
(*    | Texp_match of expression * (pattern * expression) list * partial
    | Texp_try of expression * (pattern * expression) list
    | Texp_tuple of expression list
    | Texp_construct of constructor_description * expression list
    | Texp_variant of label * expression option
    | Texp_record of (label_description * expression) list * expression option*)
    | Texp_field(e, lbl) ->
	let te = term env e in
	let fi = (label e.exp_type lbl).ml_li_field in
	JCTderef(make_term te (make e.exp_type), LabelNone, fi)
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
	JCTvar(Jc_pervasives.var (make e.exp_type) "\\result")
    | Texp_old e ->
	JCTold(make_term (term env e) (make e.exp_type))
    | Texp_implies(a, b) ->
	JCTif(
	  make_term (term env a) (make a.exp_type),
	  make_term (term env b) (make b.exp_type),
	  make_term (JCTconst (JCCboolean true)) (JCTnative Tboolean))
    | _ -> not_implemented e.exp_loc "ml_interp.ml: term"

let rec assertion env e =
  match e.exp_desc with
    | Texp_ident _ ->
	JCAbool_term(make_term (term env e) (make e.exp_type))
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
		    JCAbool_term(make_term (term env e) (make e.exp_type))
	      end
	  | _ -> not_implemented e.exp_loc "unsupported application (assertion)"
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
    | Texp_result
    | Texp_old _ ->
	assert false (* impossible *)
    | Texp_implies(a, b) ->
	JCAimplies(
	  make_assertion (assertion env a),
	  make_assertion (assertion env b))
    | _ -> not_implemented e.exp_loc "ml_interp.ml: assertion"

type jessie_or_caml_expr =
  | Jessie_expr of Jc_ast.texpr
  | Caml_expr of Ml_ocaml.Typedtree.expression

let try_expression env e =
  try
    Jessie_expr(make_expr (expression env e) (make e.exp_type))
  with Not_an_expression ->
    Caml_expr e

let rec statement env e cont =
  match e.exp_desc with
    | Texp_ident _
    | Texp_constant _ ->
	cont (make_expr (expression env e) (make e.exp_type))
    | Texp_let((Nonrecursive | Default),
	       [ { pat_desc = Tpat_var id }, eq_expr ], in_expr) ->
	let new_env, vi =
	  Ml_env.add_var (name id) (make eq_expr.exp_type) env
	in
	let in_ty = make in_expr.exp_type in
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
(*    | Texp_function of (pattern * expression) list * partial*)
    | Texp_apply(f, args) ->
	let args = list_filter_option (List.map fst args) in
	let args_try = List.map (try_expression env) args in
	let args_final = List.map
	  (function
	     | Jessie_expr e -> e
	     | Caml_expr e -> not_implemented e.exp_loc
		 "while loop in argument")
	  args_try
	in
	cont (match f.exp_desc with
	  | Texp_ident(Pident id, { val_kind = Val_reg }) ->
	      apply_op_expr id args_final (binary_op_expr e.exp_loc)
		(fun x -> let fi = try
		   Ml_env.find_fun x env
		 with
		   | Ml_env.Not_found_str x -> locate_error e.exp_loc
		       "unknown function: %s" x
		 in
		 make_expr (JCTEcall(fi, args_final))
		   fi.jc_fun_info_result.jc_var_info_type)
	  | _ -> not_implemented e.exp_loc "unsupported application (statement)"
	)
    | Texp_match(me, pel, partial) ->
	statement env me
	  (fun res ->
	     make_var_tmp (make me.exp_type) (Some res)
	       (fun _ arg ->
		  make_var_tmp (make e.exp_type) None
		    (fun resvi rese ->
		       make_statement_block [
			 (let pfl = List.map
			   (fun (pat, e) ->
			      pat,
			      (fun env -> statement env e (make_affect resvi)))
			   pel
			 in
			 let catchall = match partial with
			   | Partial -> not_implemented e.exp_loc
			       "partial pattern-matching (statement)"
			   | Total -> None
			 in
			 PatStatement.pattern_expr_list env arg pfl catchall);
			 cont rese
		       ])))
(*    | Texp_try of expression * (pattern * expression) list*)
    | Texp_tuple el ->
	let si = structure e.exp_type in
	make_alloc_tmp si
	  (fun _ tmp_e ->
	     make_statement_block [
	       statement_list env el
		 (list_mapi
		    (fun i _ ->
		       let fi = proj e.exp_type i in
		       make_affect_field tmp_e fi)
		    el);
	       cont tmp_e;
	     ])
    | Texp_construct(cd, el) ->
	let ci = constructor e.exp_type cd in
	make_alloc_tmp ci.ml_ci_structure
	  (fun _ tmp_e ->
	     make_statement_block [
	       make_affect_field tmp_e ci.ml_ci_tag_field
		 (expr_of_int ci.ml_ci_tag);
	       statement_list env el
		 (List.map (fun fi -> make_affect_field tmp_e fi)
		    ci.ml_ci_arguments);
	       cont tmp_e;
	     ])
(*    | Texp_variant of label * expression option*)
    | Texp_record(lel, None) ->
	let si = structure e.exp_type in
	make_alloc_tmp si
	  (fun _ tmp_e ->
	     make_statement_block [
	       statement_list env (List.map snd lel)
		 (List.map
		    (fun (ld, _) ->
		       let li = label e.exp_type ld in
		       make_affect_field tmp_e li.ml_li_field)
		    lel);
	       cont tmp_e;
	     ])
    | Texp_record(_, Some _) ->
	not_implemented e.exp_loc "record with"
    | Texp_field(e, lbl) ->
	let fi = (label e.exp_type lbl).ml_li_field in
	statement env e
	  (fun res -> cont
	     (make_expr (JCTEderef(res, fi))
		fi.jc_field_info_type))
    | Texp_setfield(e, lbl, v) ->
	let fi = (label e.exp_type lbl).ml_li_field in
	statement env e
	  (fun res ->
	     statement env v
	       (fun res2 -> cont
		  (make_expr (JCTEassign_heap(res, fi, res2))
		     (JCTnative Tunit))))
(*    | Texp_array of expression list*)
    | Texp_ifthenelse(if_expr, then_expr, else_expr) ->
	let ty = make then_expr.exp_type in
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
    | Texp_while(cond, annot, body) ->
	let annot = {
	  jc_loop_tag = fresh_int ();
	  jc_loop_invariant =
	    (match annot.ws_invariant with
	       | None -> make_assertion JCAtrue
	       | Some x -> make_assertion (assertion env x)); 
	  jc_loop_variant =
	    (match annot.ws_variant with
	       | None -> None
	       | Some x -> Some(
		   make_term (term env x) (make x.exp_type)));
	} in
	statement env cond
	  (fun e -> make_statement_block [
	     make_statement (JCTSwhile("", e, annot,
				       statement env body make_discard));
	     cont void;
	   ])
(*    | Texp_for of
	Ident.t * expression * expression * direction_flag * expression
    | Texp_when of expression * expression
    | Texp_send of expression * meth
    | Texp_new of Path.t * class_declaration
    | Texp_instvar of Path.t * Path.t
    | Texp_setinstvar of Path.t * Path.t * expression
    | Texp_override of Path.t * (Path.t * expression) list
    | Texp_letmodule of Ident.t * module_expr * expression*)
    | Texp_assert e ->
	make_statement_block [
	  make_statement (JCTSassert (make_assertion (assertion env e)));
	  cont void;
	]
    | Texp_assertfalse ->
	make_statement_block [
	  make_statement (JCTSassert (make_assertion JCAfalse));
	  cont void;
	]
(*    | Texp_lazy of expression
    | Texp_object of class_structure * class_signature * string list *)
    | Texp_result
    | Texp_old _ ->
	assert false (* impossible *)
    | _ -> not_implemented e.exp_loc "ml_interp.ml: statement"

and statement_list env l conts =
  let stl = List.fold_left2
    (fun stl e cont -> match e with
       | Jessie_expr e -> (cont e)::stl
       | Caml_expr e -> (statement env e cont)::stl)
    []
    (List.map (try_expression env) l)
    conts
  in
  make_statement_block (List.rev stl)

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

let invariants env spec (*struct_info*) =
  list_fold_map
    (fun env i ->
       let ty = make_pointer_type dummy_struct(*struct_info*) in
       let arg_vi, body = match i.ti_argument.pat_desc with
	 | Tpat_var id ->
	     let arg_name = name id in
	     let body_env, vi = Ml_env.add_var arg_name ty env in
	     vi, make_assertion (assertion body_env i.ti_body)
	 | _ ->
	     let _, vi = Ml_env.add_var "jessica_arg" ty env in
	     let cond, body = PatAssertion.pattern_expr
	       env
	       (make_var_term vi)
	       i.ti_argument
	       (fun env -> make_assertion (assertion env i.ti_body))
	     in
	     let conda = make_assertion (JCAbool_term cond) in
	     vi, make_implies conda body
       in
       let final_env, _ =
	 Ml_env.add_logic_fun (name i.ti_name) [ arg_vi ] None env
       in
       final_env, (name i.ti_name, arg_vi, body))
    env
    spec.ts_invariants
  
(*let record_decl env (id, labels) =
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
       Ml_env.add_field lbl (make ty) struct_info env)
    env
    labels
  in
  struct_info.jc_struct_info_fields <- field_infos;
  log "      Invariants...";
  let env, invariants = invariants env spec struct_info in
  Ml_env.add_struct struct_info env, (* replace existing structure *)
  JCstruct_def(struct_name, None, field_infos, invariants)

let variant_decl env (id, constrs) =
  log "    Variant type %s:" (name id);
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
  log "      Constructors...";
  let env, tag_fi = Ml_env.add_tag struct_info env in
  let env, field_infos = list_fold_mapi
    (fun env i (c, tyl) ->
       Ml_env.add_constructor c (List.map (make) tyl) struct_info i env)
    env
    constrs
  in
  let field_infos = tag_fi :: (List.flatten field_infos) in
  struct_info.jc_struct_info_fields <- field_infos;
  log "      Invariants...";
  let env, invariants = invariants env spec struct_info in
  Ml_env.add_struct struct_info env, (* replace existing structure *)
  [(* JCenum_type_def(
      enum_info.jc_enum_info_name,
      enum_info.jc_enum_info_min,
      enum_info.jc_enum_info_max);*)
    JCstruct_def(struct_name, None, field_infos, invariants) ]

let pre_declare_type name env =
  let si = {
    jc_struct_info_name = name; (* only this field is important *)
    jc_struct_info_parent = None;
    jc_struct_info_root = name;
    jc_struct_info_fields = [];
  } in
  Ml_env.add_struct si env*)

let rec function_decl env e = match e.exp_desc with
  | Texp_function([ { pat_desc = Tpat_var pid;
		      pat_type = pty },
		    body ], _) ->
      let params, body' = function_decl env body in
      (pid, pty)::params, body'
  | _ -> [], e

let rec read_location_set env = function
  | RLvar id ->
      JCLSvar(Ml_env.find_var (Ml_ocaml.Path.name id) env)
  | RLderef(rl, ld) ->
      not_implemented Ml_ocaml.Location.none "deref in reads"

let rec read_location env = function
  | RLvar id ->
      JCLvar(Ml_env.find_var (Ml_ocaml.Path.name id) env)
  | RLderef(rl, ld) ->
      not_implemented Ml_ocaml.Location.none "deref in reads"

let structure_item env = function
  | Tstr_value(recflag, [ { pat_desc = Tpat_var id },
		    ({ exp_desc = Texp_function _ } as expr) ]) ->
      let fun_name = identifier_of_symbol (name id) in
      log "    Function %s (%s):" (name id) fun_name;
      let params, body = function_decl env expr in
      log "      Looking for spec...";
      let spec =
	try
	  Ml_env.find_fun_spec id env
	with Ml_env.Not_found_str _ ->
	  log "        Not found";
	  {
	    fs_function = Pident id; (* unused *)
	    fs_arguments = []; (* unused *)
	    fs_requires = None;
	    fs_behaviors = [];
	  }
      in
      log "      Return type...";
      let return_type = make body.exp_type in
      log "      Building environment...";
      let new_env, params' = list_fold_map
	(fun env (pid, pty) -> Ml_env.add_var (name pid) (make pty) env)
	env
	params
      in
      let body_env = match recflag with
	| Nonrecursive
	| Default ->
	    new_env
	| Recursive ->
	    Ml_env.add_fun (name id) params' return_type new_env
      in
      log "      Body...";
      let body' = statement body_env body
	(if is_unit return_type then make_discard else make_return)
      in
      log "      Requires...";
      let requires = match spec.fs_requires with
	| None -> JCAtrue
	| Some x -> assertion body_env x
      in
      log "      Behaviors...";
      let behaviors = List.map (behavior body_env) spec.fs_behaviors in
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
	  fun_name,
	  params',
	  jc_spec,
	  Some [ body' ]
	)
      in
      [ jc_fun_def ], Ml_env.add_fun (name id) params' return_type env
  | Tstr_type l ->
      List.iter (fun (id, td) -> declare id td false) l;
      [], env
  | Tstr_function_spec _ -> [], env (* done before (see add_structure_specs) *)
  | Tstr_type_spec ({ ts_type = Pident id } as spec) ->
      let env, invariants = invariants env spec in
      List.iter (add_invariant id) invariants;
      [], env
  | Tstr_logic_function_spec lfs ->
      begin match lfs.lfs_arguments with
	| [] ->
	    (* logic constant *)
	    let ty = make lfs.lfs_return_type in
	    let id = name lfs.lfs_name in
	    [ JClogic_const_def(
		ty,
		id,
		match lfs.lfs_body with
		  | OBbody e -> Some(make_term (term env e) (make e.exp_type))
		  | OBreads [] -> None
		  | OBreads _ -> assert false) ],
	    fst (Ml_env.add_var id ty env)
	| _ ->
	    (* logic function *)
	    let rty = if lfs.lfs_predicate then None else
	      Some(make lfs.lfs_return_type) in
	    let id = name lfs.lfs_name in
	    let body_env, args = list_fold_mapi
	      (fun env i -> function
		 | { pat_desc = Tpat_var id; pat_type = ty } ->
		     Ml_env.add_var (name id) (make ty) env
		 | { pat_loc = loc } ->
		     not_implemented loc "pattern in logic function argument")
	      env
	      lfs.lfs_arguments
	    in
	    [ JClogic_fun_def(
		rty,
		id,
		[],
		args,
		match lfs.lfs_body with
		  | OBbody e ->
		      JCTerm(make_term (term body_env e) (make e.exp_type))
		  | OBreads rl ->
		      JCReads(List.map (read_location body_env) rl)) ],
	    fst (Ml_env.add_logic_fun id args rty env)
      end
  | Tstr_logic_type_spec(id, td) ->
      declare id td true;
      [], env
  | Tstr_axiom_spec axs ->
      let body_env, args = list_fold_mapi
	(fun env i pat ->
	   Ml_env.add_var "jessica_arg" (make pat.pat_type) env)
	env
	axs.as_arguments
      in
      let cond, _, body = PatAssertion.pattern_list_expr
	env
	(List.map make_var_term args)
	axs.as_arguments
	(fun env -> make_assertion (assertion env axs.as_body))
      in
      let conda = make_assertion (JCAbool_term cond) in
      let a = make_assertion (JCAimplies(conda, body)) in
      let qa = List.fold_left
	(fun acc vi -> make_assertion (JCAquantifier(Forall, vi, acc)))
	a
	args
      in
      [ JCaxiom_def(axs.as_name, qa) ], env
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

(*let add_type_specs env = List.fold_left
  (fun env -> function
     | Tstr_type_spec ({ ts_type = Pident id } as spec) ->
	 Ml_env.add_type_spec id spec env
     | _ -> env)
  env*)

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
