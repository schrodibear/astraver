open Ml_misc
open Jc_env
open Jc_ast
open Ml_ocaml.Typedtree
open Ml_ocaml.Ident
open Ml_type
open Ml_env
open Ml_constant

let rec pattern env pat =
  let newenv, node = match pat.pat_desc with
    | Tpat_any ->
	env, JCPany
    | Tpat_var id ->
	let env, vi = add_var (name id) (make pat.pat_type) env in
	env, JCPvar vi
    | Tpat_alias(p, id) ->
	let env, p = pattern env p in
	let env, vi = add_var (name id) (make pat.pat_type) env in
	env, JCPas(p, vi)
    | Tpat_constant c ->
	env, JCPconst(constant c)
    | Tpat_tuple pl ->
	let si = structure pat.pat_type in
	let env, fpl = list_fold_mapi
	  (fun env i p ->
	     let env, p = pattern env p in
	     env, (proj pat.pat_type i, p))
	  env pl
	in
	env, JCPstruct(si, fpl)
    | Tpat_construct(cd, pl) ->
	let ci = constructor pat.pat_type cd in
	let env, fpl = list_fold_map2
	  (fun env fi p ->
	     let env, p = pattern env p in
	     env, (fi, p))
	  env ci.ml_ci_arguments pl
	in
	env, JCPstruct(ci.ml_ci_structure, fpl)
    | Tpat_variant _ ->
	assert false (* TODO *)
    | Tpat_record lpl ->
	let si = structure pat.pat_type in
	let env, fpl = list_fold_map
	  (fun env (l, p) ->
	     let li = label pat.pat_type l in
	     let env, p = pattern env p in
	     env, (li.ml_li_field, p))
	  env lpl
	in
	env, JCPstruct(si, fpl)
    | Tpat_array _ ->
	assert false (* TODO *)
    | Tpat_or(p1, p2, _) ->
	let _, p1 = pattern env p1 in
	let env, p2 = pattern env p2 in
	env, JCPor(p1, p2)
  in newenv, {
    jc_pattern_node = node;
    jc_pattern_loc = Loc.dummy_position;
    jc_pattern_type = JCTnull;
  }

let pattern_term env body pat =
  let ty = make pat.pat_type in
  match pat.pat_desc with
    | Tpat_var id ->
	let benv, vi = Ml_env.add_var (name id) ty env in
	vi, body benv
    | _ ->
	let _, vi = Ml_env.add_var "jessica_arg" ty env in
	let benv, tpat = pattern env pat in
	let matchterm =
	  JCTmatch(
	    make_term (JCTvar vi) ty,
	    [ tpat, body benv ]
	  )
	in
	vi, make_bool_term matchterm
(*
let rec pattern_list_term env body pats =
  List.fold_right
    (fun pat (vars, body) ->
       let vi, tpat = pattern_term env body pat in
       vi::vars, 

let rec pattern_list_term env body = function
  | [] ->
      [], body env
  | pat::rem ->
      let vi, body =
	pattern_term env
	  (fun env -> pattern_list_term env body rem)
	  pat
      in
*)
let pattern_list_term _ = assert false      

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
