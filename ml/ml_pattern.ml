(* Interpretation of pattern-matching *)

open Ml_misc
open Ml_constant
open Ml_ocaml.Typedtree
open Ml_ocaml.Types
open Ml_ocaml.Ident
open Ml_type
open Jc_ast
open Jc_env

let rec pattern_assertion env arg pat =
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
	  "ml_pattern.ml: pattern_assertion: or-pattern with path"

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
