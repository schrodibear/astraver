(* Interpretation of pattern-matching *)

open Ml_misc
open Ml_constant
open Ml_ocaml.Typedtree
open Ml_ocaml.Types
open Ml_ocaml.Ident
open Ml_type
open Jc_ast
open Jc_env

(*let rec pattern_assertion env arg pat =
  let ty = Ml_type.make pat.pat_type in
  match pat.pat_desc with
    | Tpat_any ->
	env, [], make_assertion JCAtrue
    | Tpat_var id ->
	let env, vi = Ml_env.add_var (name id) ty env in
	env,
	[ vi ],
	make_eq_assertion (make_var_term vi) arg
    | Tpat_alias(pat, id) ->
	let env, pat_vars, pat_tr = pattern_assertion env arg pat in
	let env, vi = Ml_env.add_var (name id) ty env in
	env,
	vi::pat_vars,
	make_and
	  (make_eq_assertion (make_var_term vi) arg)
	  pat_tr
    | Tpat_constant c ->
	env,
	[],
	make_eq_assertion arg (constant_term c)
    | Tpat_tuple _ ->
	not_implemented pat.pat_loc
	  "ml_pattern.ml: pattern_assertion: tuples"
    | Tpat_construct(cd, pl) ->
	let ci = constructor pat.pat_type cd in
	let env, tpl = list_fold_mapi
	  (fun env i pat ->
	     let fi = List.nth ci.ml_ci_arguments i in
	     let arg = make_term
	       (JCTderef(arg, fi))
	       fi.jc_field_info_type
	     in
	     let env, vars, tpat = pattern_assertion env arg pat in
	     env, (vars, tpat))
	  env
	  pl
	in
	let vars = List.fold_left (fun acc (b, _) -> acc @ b) [] tpl in
	let tag_cond = make_eq_assertion
	  (make_int_term (JCTderef(arg, ci.ml_ci_tag_field)))
	  (make_int_term (JCTconst(JCCinteger (string_of_int ci.ml_ci_tag))))
	in
	let tr = make_and_list (tag_cond :: (List.map snd tpl)) in
	env, vars, tr
    | Tpat_variant _ ->
	not_implemented pat.pat_loc
	  "ml_pattern.ml: pattern_assertion: polymorphic variants"
    | Tpat_record lbls ->
	List.fold_left
	  (fun (env, vars, tr) (ld, pat2) ->
	     let li = label pat.pat_type ld in
	     let fi = li.ml_li_field in
	     let arg_fi = make_term (JCTderef(arg, fi)) fi.jc_field_info_type in
	     let pat_env, pat_vars, pat_tr = pattern_assertion env arg_fi pat2 in
	     pat_env, vars @ pat_vars, make_and tr pat_tr)
	  (env, [], make_assertion JCAtrue)
	  lbls
    | Tpat_array _ ->
	not_implemented pat.pat_loc
	  "ml_pattern.ml: pattern_assertion: arrays"
    | Tpat_or(p1, p2, None) ->
	(* p1 and p2 have the same variables *)
	let env, vars, p1_tr = pattern_assertion env arg p1 in
	let env, _, p2_tr = pattern_assertion env arg p2 in
	env,
	vars,
	make_or p1_tr p2_tr
    | Tpat_or(p1, p2, Some path) ->
	not_implemented pat.pat_loc
	  "ml_pattern.ml: pattern_assertion: or-pattern with path"*)

module type TPatternArg = sig
  type t
  type expr
  type condition
  val make_if: condition -> t -> t -> t
  val make_if_expr: condition -> expr -> expr -> expr
  val make_var: Jc_env.var_info -> expr -> t -> t
  val make_equal: expr -> expr -> condition
  val make_and: condition -> condition -> condition
  val make_or: condition -> condition -> condition
  val make_deref: expr -> Jc_env.field_info -> expr
  val make_constant: Ml_ocaml.Asttypes.constant -> expr
  val make_bool: bool -> condition
  val make_int: int -> expr
end

module PAStatement = struct
  type t = Jc_ast.tstatement
  type expr = Jc_ast.texpr
  type condition = Jc_ast.texpr
  let make_if cond th el =
    make_statement (JCTSif(cond, th, el))
  let make_if_expr cond th el =
    make_expr (JCTEif(cond, th, el)) th.jc_texpr_type
  let make_var vi init body =
    make_statement (JCTSdecl(vi, Some init, body))
  let make_equal = make_eq_expr
  let make_and = make_and_expr
  let make_or = make_or_expr
  let make_deref x fi =
    make_expr (JCTEderef(x, fi)) fi.jc_field_info_type
  let make_constant = constant_expr
  let make_bool b = make_bool_expr (JCTEconst(JCCboolean b))
  let make_int i = make_int_expr (JCTEconst(JCCinteger(string_of_int i)))
end

module PAExpression = struct
  type t = Jc_ast.texpr
  type expr = Jc_ast.texpr
  type condition = Jc_ast.texpr
  let make_if cond th el =
    make_expr (JCTEif(cond, th, el)) th.jc_texpr_type
  let make_if_expr cond th el =
    make_expr (JCTEif(cond, th, el)) th.jc_texpr_type
  let make_var vi init body =
    make_expr (JCTElet(vi, init, body)) body.jc_texpr_type
  let make_equal = make_eq_expr
  let make_and = make_and_expr
  let make_or = make_or_expr
  let make_deref x fi =
    make_expr (JCTEderef(x, fi)) fi.jc_field_info_type
  let make_constant = constant_expr
  let make_bool b = make_bool_expr (JCTEconst(JCCboolean b))
  let make_int i = make_int_expr (JCTEconst(JCCinteger(string_of_int i)))
end

module PAAssertion = struct
  type t = Jc_ast.assertion
  type expr = Jc_ast.term
  type condition = Jc_ast.term
  let make_if cond th el =
    make_assertion (JCAif(cond, th, el))
  let make_if_expr cond th el =
    make_term (JCTif(cond, th, el)) th.jc_term_type
  let make_var vi init body =
    let body = make_implies (make_eq_assertion (make_var_term vi) init) body in
    make_assertion (JCAquantifier(Forall, vi, body))
  let make_equal = make_eq_term
  let make_and = make_and_term
  let make_or = make_or_term
  let make_deref x fi =
    make_term (JCTderef(x, fi)) fi.jc_field_info_type
  let make_constant = constant_term
  let make_bool b = make_bool_term (JCTconst(JCCboolean b))
  let make_int i = make_int_term (JCTconst(JCCinteger(string_of_int i)))
end

module type TPatternF = functor (A: TPatternArg) -> sig
  val pattern: Ml_env.t -> A.expr -> Ml_ocaml.Typedtree.pattern ->
    A.condition * Ml_env.t * (Jc_env.var_info * A.expr) list

  val pattern_expr: Ml_env.t -> A.expr -> Ml_ocaml.Typedtree.pattern ->
    (Ml_env.t -> A.t) -> A.condition * A.t

  val pattern_expr_list: Ml_env.t -> A.expr ->
    (Ml_ocaml.Typedtree.pattern * (Ml_env.t -> A.t)) list -> A.t option -> A.t
end

module Pattern: TPatternF = functor (A: TPatternArg) -> struct
  open A

  let sort_vars = List.sort
    (fun (v1, _) (v2, _) ->
       String.compare v1.jc_var_info_name v2.jc_var_info_name)

  let rec pattern env arg pat =
    let ty = Ml_type.make pat.pat_type in
    match pat.pat_desc with
      | Tpat_any ->
	  make_bool true, env, []
      | Tpat_var id ->
	  let env2, vi = Ml_env.add_var (name id) ty env in
	  make_bool true, env2, [ vi, arg ]
      | Tpat_alias(pat2, id) ->
	  let cond, env2, vars = pattern env arg pat2 in
	  let env3, vi = Ml_env.add_var (name id) ty env2 in
	  cond, env3, (vi, arg)::vars
      | Tpat_constant c ->
	  make_equal arg (make_constant c), env, []
      | Tpat_tuple _ ->
	  not_implemented pat.pat_loc "tuple pattern"
      | Tpat_construct(cd, pl) ->
	  let ci = constructor pat.pat_type cd in
	  let cond, env2, vars = List.fold_left2
	    (fun (cond, env2, vars) lpat fi ->
	       let cond2, env3, vars2 = pattern env2 (make_deref arg fi) lpat in
	       make_and cond cond2, env3, vars @ vars2)
	    (make_bool true, env, [])
	    pl
	    ci.ml_ci_arguments
	  in
	  let tag = make_int ci.ml_ci_tag in
	  let cond2 = make_and
	    (make_equal (make_deref arg ci.ml_ci_tag_field) tag)
	    cond
	  in
	  cond2, env2, vars
      | Tpat_variant _ ->
	  not_implemented pat.pat_loc "polymorphic variant pattern"
      | Tpat_record lbls ->
	  List.fold_left
	    (fun (cond, env2, vars) (ld, lpat) ->
	       let fi = (label pat.pat_type ld).ml_li_field in
	       let cond2, env3, vars2 = pattern env2 (make_deref arg fi) lpat in
	       make_and cond cond2, env3, vars @ vars2)
	    (make_bool true, env, [])
	    lbls
      | Tpat_array _ ->
	  not_implemented pat.pat_loc "array pattern"
      | Tpat_or(pat1, pat2, None) ->
	  let cond1, env2, vars1 = pattern env arg pat1 in
	  let cond2, _, vars2 = pattern env arg pat2 in
	  (* OCaml typing ensures that vars1 and vars2 contain the same
          variable names. *)
	  let vars = List.map2
	    (fun (vi, val1) (_, val2) -> vi, make_if_expr cond1 val1 val2)
	    (sort_vars vars1)
	    (sort_vars vars2)
	  in
	  make_or cond1 cond2, env2, vars
      | Tpat_or(_, _, Some _) ->
	  not_implemented pat.pat_loc "or pattern with path"

  let pattern_expr env arg pat body =
    let cond, env2, vars = pattern env arg pat in
    let final_body = List.fold_left
      (fun acc (vi, init) -> make_var vi init acc)
      (body env2)
      vars
    in
    cond, final_body

  let pattern_expr_list env arg pel catchall =
    let cbl = List.map (fun (pat, body) -> pattern_expr env arg pat body) pel in
    match catchall with
      | Some x ->
	  List.fold_right (fun (cond, body) acc -> make_if cond body acc) cbl x
      | None ->
	  match List.rev cbl with
	    | [] -> assert false
	    | (_, last_body)::tl ->
		List.fold_left
		  (fun acc (cond, body) -> make_if cond body acc) last_body tl
end

module PatStatement = Pattern(PAStatement)
module PatExpression = Pattern(PAExpression)
module PatAssertion = Pattern(PAAssertion)

(*let rec pattern_expr env arg pat =
  let ty = Ml_type.make pat.pat_type in
  match pat.pat_desc with
    | Tpat_any ->
	env, [], make_bool_expr (JCTEconst(JCCboolean true))
    | Tpat_var id ->
	let env, vi = Ml_env.add_var (name id) ty env in
	env,
	[ vi ],
	make_eq_expr (make_var_expr vi) arg
    | Tpat_alias(pat, id) ->
	let env, pat_vars, pat_tr = pattern_expr env arg pat in
	let env, vi = Ml_env.add_var (name id) ty env in
	env,
	vi::pat_vars,
	make_and_expr
	  (make_eq_expr (make_var_expr vi) arg)
	  pat_tr
    | Tpat_constant c ->
	env,
	[],
	make_eq_expr arg (constant_expr c)
    | Tpat_tuple _ ->
	not_implemented pat.pat_loc
	  "ml_pattern.ml: pattern_expr: tuples"
    | Tpat_construct(cd, pl) ->
	let ci = constructor pat.pat_type cd in
	let env, tpl = list_fold_mapi
	  (fun env i pat ->
	     let fi = List.nth ci.ml_ci_arguments i in
	     let arg = make_expr
	       (JCTEderef(arg, fi))
	       fi.jc_field_info_type
	     in
	     let env, vars, tpat = pattern_expr env arg pat in
	     env, (vars, tpat))
	  env
	  pl
	in
	let vars = List.fold_left (fun acc (b, _) -> acc @ b) [] tpl in
	let tag_cond = make_eq_expr
	  (make_int_expr (JCTEderef(arg, ci.ml_ci_tag_field)))
	  (make_int_expr (JCTEconst(JCCinteger (string_of_int ci.ml_ci_tag))))
	in
	let tr = make_and_list_expr (tag_cond :: (List.map snd tpl)) in
	env, vars, tr
    | Tpat_variant _ ->
	not_implemented pat.pat_loc
	  "ml_pattern.ml: pattern_expr: polymorphic variants"
    | Tpat_record lbls ->
	List.fold_left
	  (fun (env, vars, tr) (ld, pat2) ->
	     let li = label pat.pat_type ld in
	     let fi = li.ml_li_field in
	     let arg_fi = make_expr (JCTEderef(arg, fi))
	       fi.jc_field_info_type in
	     let pat_env, pat_vars, pat_tr = pattern_expr env arg_fi pat2 in
	     pat_env, vars @ pat_vars, make_and_expr tr pat_tr)
	  (env, [], make_bool_expr (JCTEconst (JCCboolean true)))
	  lbls
    | Tpat_array _ ->
	not_implemented pat.pat_loc
	  "ml_pattern.ml: pattern_expr: arrays"
    | Tpat_or(p1, p2, None) ->
	(* p1 and p2 have the same variables *)
	let env, vars, p1_tr = pattern_expr env arg p1 in
	let env, _, p2_tr = pattern_expr env arg p2 in
	env,
	vars,
	make_or_expr p1_tr p2_tr
    | Tpat_or(p1, p2, Some path) ->
	not_implemented pat.pat_loc
	  "ml_pattern.ml: pattern_expr: or-pattern with path"

let pattern_expr_list expr pattern env arg pel =
  List.map
    (fun (p, e) ->
       let env, vars, tr = pattern env arg p in
       vars, tr, expr env e)
    pel*)

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
