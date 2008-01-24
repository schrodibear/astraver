(* Interpretation of pattern-matching *)

open Ml_misc
open Ml_constant
open Ml_ocaml.Typedtree
open Ml_ocaml.Types
open Ml_ocaml.Ident
open Ml_type
open Jc_ast
open Jc_env

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

module type TPattern = sig
  type t
  type expr
  type condition

  val pattern: Ml_env.t -> expr -> Ml_ocaml.Typedtree.pattern ->
    condition * Ml_env.t * (Jc_env.var_info * expr) list

  val pattern_expr: Ml_env.t -> expr -> Ml_ocaml.Typedtree.pattern ->
    (Ml_env.t -> t) -> condition * t

  val pattern_expr_list: Ml_env.t -> expr ->
    (Ml_ocaml.Typedtree.pattern * (Ml_env.t -> t)) list -> t option -> t

  val pattern_list: Ml_env.t -> expr list -> Ml_ocaml.Typedtree.pattern list ->
    condition * Ml_env.t * (Jc_env.var_info * expr) list

  val pattern_list_expr: Ml_env.t -> expr list ->
    Ml_ocaml.Typedtree.pattern list -> (Ml_env.t -> t) ->
    condition * Ml_env.t * t
end

module type TPatternF = functor (A: TPatternArg) ->
  TPattern
    with type t = A.t
    with type expr = A.expr
    with type condition = A.condition

module Pattern: TPatternF = functor (A: TPatternArg) -> struct
  type t = A.t
  type expr = A.expr
  type condition = A.condition

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
      | Tpat_tuple pl ->
	  list_fold_lefti
	    (fun i (cond, env2, vars) pat2 ->
	       let fi = proj pat.pat_type i in
	       let cond2, env3, vars2 = pattern env2 (make_deref arg fi) pat2 in
	       make_and cond cond2, env3, vars @ vars2)
	    (make_bool true, env, [])
	    pl
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

  let quantify =
    List.fold_left
      (fun acc (vi, init) -> make_var vi init acc)

  let pattern_expr env arg pat body =
    let cond, env2, vars = pattern env arg pat in
    let final_body = quantify (body env2) vars in
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

  let pattern_list env args pats =
    List.fold_right2
      (fun pat arg (cond, env2, vars) ->
	 let cond2, env3, vars2 = pattern env2 arg pat in
	 make_and cond cond2, env3, vars @ vars2)
      pats
      args
      (make_bool true, env, [])

  let pattern_list_expr env args pats body =
    let cond, env2, vars = pattern_list env args pats in
    let final_body = quantify (body env2) vars in
    cond, env2, final_body
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
    make_term (JCTderef(x, LabelNone, fi)) fi.jc_field_info_type
  let make_constant = constant_term
  let make_bool b = make_bool_term (JCTconst(JCCboolean b))
  let make_int i = make_int_term (JCTconst(JCCinteger(string_of_int i)))
end

module PatStatement = Pattern(PAStatement)
module PatExpression = Pattern(PAExpression)
module PatAssertion = Pattern(PAAssertion)

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
