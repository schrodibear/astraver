(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: mlize.ml,v 1.15 2002-03-11 15:17:57 filliatr Exp $ i*)

open Ident
open Logic
open Misc
open Types
open Ast
open Util
open Rename
open Env
open Effect
open Typing
open Monad

(*i
let has_proof_part ren env c =
  let sign = Pcicenv.trad_sign_of ren env in
  let ty = Typing.type_of (Global.env_of_context sign) Evd.empty c in
  is_matching (Coqlib.build_coq_sig_pattern ()) ty
i*)

(* main part: translation of imperative programs into functional ones.
 * 
 * [env] is the environment
 * [ren] is the current renamings of variables
 * [t] is the imperative program to translate, annotated with type+effects
 *
 * we return the translated program in type [cc_term]
 *)

let rec trad ren t =
  let env = t.info.env in
  let ren = push_date ren t.info.label in
  trad_desc ren env t.info.kappa t.desc

and trad_desc ren env ct d =
  let (rest,tt),eft,pt,qt = decomp_kappa ct in
  match d with

  | Expression c ->
      let ids = get_reads eft in
      let al = current_vars ren ids in
      let c' = subst_in_term al c in
  (*i if has_proof_part ren env c' then
	CC_expr c'
      else i*)
      	let ty = trad_ml_type_v ren env tt in
	let t,_ =
	  result_tuple ren (current_date ren) env (rest,CC_expr c',ty) (eft,qt)
	in
	t

  | Var id ->
      if is_reference env id then
	invalid_arg "Mlise.trad_desc"
      else if is_local env id then
	CC_var id
      else
	CC_expr (Tvar id)

  | Acc _ ->
      failwith "Mlise.trad: pure terms are supposed to be expressions"

  | TabAcc (check, x, e1) ->
      let _,ty_elem = array_info env x in
      let te1 = trad ren e1 in
      let (_,ef1,p1,q1) = decomp_kappa e1.info.kappa in
      let w = get_writes ef1 in
      let ren' = next ren w in
      let id = Ident.create "index" in
      let access = 
	make_raw_access env (x,current_var ren' x) (Tvar id) 
      in
      let t,ty = result_tuple ren' (current_date ren) env
		   (rest, CC_expr access, CC_type) (eft,qt) in
      let t =
	if check then 
	  let h = make_pre_access env x (Tvar id) in 
	  let_in_pre ty (anonymous_pre true h) t
	else
	  t 
      in
      make_let_in ren ren' env te1 p1
	(current_vars ren' w,q1) (id, PureType PTint) (t,ty)

  | Aff (x, e1) ->
      let tx = type_in_env env x (*i trad_type_in_env ren env x i*) in
      let te1 = trad ren e1 in
      let (_,ef1,p1,q1) = decomp_kappa e1.info.kappa in
      let w1 = get_writes ef1 in
      let ren' = next ren (x::w1) in
      let t_ty = 
	result_tuple ren' (current_date ren) env
	  (rest, CC_expr (Tconst ConstUnit), CC_type) (eft,qt) 
      in
      make_let_in ren ren' env te1 p1
	(current_vars ren' w1,q1) (current_var ren' x,tx) t_ty

  | TabAff (check, x, e1, e2) ->
      let _,ty_elem = array_info env x in
      let te1 = trad ren e1 in
      let (_,ef1,p1,q1) = decomp_kappa e1.info.kappa in
      let w1 = get_writes ef1 in
      let ren' = next ren w1 in
      let te2 = trad ren' e2 in
      let (_,ef2,p2,q2) = decomp_kappa e2.info.kappa in
      let w2 = get_writes ef2 in
      let ren'' = next ren' w2 in
      let id1 = Ident.create "index" in
      let id2 = Ident.create "v" in
      let ren''' = next ren'' [x] in
      let t,ty = result_tuple ren''' (current_date ren) env
		   (rest, CC_expr (Tconst ConstUnit), CC_type) (eft,qt) in
      let store = make_raw_store env (x,current_var ren'' x) (Tvar id1)
		   (Tvar id2) in
      let t = make_let_in ren'' ren''' env (CC_expr store) [] ([],None) 
		(current_var ren''' x, type_in_env env x) (t,ty) in
      let t = make_let_in ren' ren'' env te2 p2
     		(current_vars ren'' w2,q2) (id2,ty_elem) (t,ty) in
      let t = 
	if check then
	  let h = make_pre_access env x (Tvar id1) in
	  let_in_pre ty (anonymous_pre true h) t
	else
	  t 
      in
      make_let_in ren ren' env te1 p1
	(current_vars ren' w1,q1) (id1,PureType PTint) (t,ty)

  | Seq bl ->
      let before = current_date ren in
      let finish ren = function
	| Some (id,ty) -> 
	    result_tuple ren before env (id,CC_var id, CC_type) (eft,qt)
	| None ->
	    failwith "a block should contain at least one statement"
      in
      let bl = trad_block ren env bl in
      make_block ren env finish bl

  | If (b, e1, e2) ->
      (*i EXP: we do not generate the obligation at the end of test i*)
      let b' =
	{ b with info={ b.info with kappa={ b.info.kappa with c_post=None }}}
      in
      let tb = trad ren b' in
      let _,efb,_,_ = decomp_kappa b.info.kappa in
      let ren' = next ren (get_writes efb) in
      let te1 = trad ren' e1 in
      let te2 = trad ren' e2 in
      make_if ren env (tb,b.info.kappa) ren' (te1,e1.info.kappa) 
	(te2,e2.info.kappa) ct

  (* Translation of the while. *)

  | While (b, inv, var, bl) ->
      (*i EXP: we do not generate the obligation at the end of test i*)
      let b' =
	{ b with info={ b.info with kappa={ b.info.kappa with c_post=None }}}
      in
      let ren' = next ren (get_writes eft) in
      let tb = trad ren' b' in
      let tbl = trad_block ren' env bl in
      let var' = typed_var env var in
      make_while ren env var' (tb,b.info.kappa) tbl (inv,ct)

  | Lam (bl, e) ->
      let bl' = trad_binders ren env bl in
      let env' = traverse_binders env bl in
      let ren' = initial_renaming env' in
      let te = trans ren' e in
      CC_lam (bl', te)

  | App (f, args) ->
      let trad_arg (ren,args) = function
	| Term a ->
	    let ((_,tya),efa,_,_) as ca = decomp_kappa a.info.kappa in
	    let ta = trad ren a in
	    let w = get_writes efa in
	    let ren' = next ren w in
	    ren', ta::args
	| Refarg _ ->
	    ren, args
	| Type v -> 
	    assert false
(*i	    let c = trad_ml_type_v ren env v in
	    ren, (CC_expr c) :: args i*)
      in
      let ren',targs = List.fold_left trad_arg (ren,[]) [args] in
      let tf = trad ren' f in
      let cf = f.info.kappa in
      let c,(s,_,_),capp = effect_app ren env f [args] in
      let tc_args =
	List.combine
	  (List.rev targs)
	  (Misc.map_succeed
	     (function
		| Term x -> x.info.kappa
		| Refarg _ -> failwith "caught"
		| Type _ -> assert false
		    (*i (Ident.result,PureType mkSet),Effect.bottom,[],Nonei*))
	     [args])
      in
      make_app env ren tc_args ren' (tf,cf) (c,s,capp) ct
	
  | LetRef (x, e1, e2) ->
      let (_,v1),ef1,p1,q1 = decomp_kappa e1.info.kappa in
      let te1 = trad ren e1 in
      let tv1 = v1 (*i trad_ml_type_v ren env v1 i*) in
      let env' = add (x,Ref v1) env in
      let ren' = next ren [x] in
      let (_,v2),ef2,p2,q2 = decomp_kappa e2.info.kappa in
      let tv2 = v2 (*i trad_ml_type_v ren' env' v2 i*) in
      let te2 = trad ren' e2 in
      let ren'' = next ren' (get_writes ef2) in
      let t,ty = result_tuple ren'' (current_date ren) env'
		   (Ident.result, CC_var Ident.result, CC_type) (eft,qt) in
      let t = make_let_in ren' ren'' env' te2 p2
		(current_vars ren'' (get_writes ef2),q2)
		(Ident.result,tv2) (t,ty) in
      let t = make_let_in ren ren' env te1 p1
     		(current_vars ren' (get_writes ef1),q1) (x,tv1) (t,ty) 
      in
      t

  | LetIn (x, e1, e2) ->
      let (_,v1),ef1,p1,q1 = decomp_kappa e1.info.kappa in
      let te1 = trad ren e1 in
      let tv1 = v1 (*i trad_ml_type_v ren env v1 i*) in
      let env' = add (x,v1) env in
      let ren' = next ren (get_writes ef1) in
      let (_,v2),ef2,p2,q2 = decomp_kappa e2.info.kappa in
      let tv2 = v2 (*i trad_ml_type_v ren' env' v2 i*) in
      let te2 = trad ren' e2 in
      let ren'' = next ren' (get_writes ef2) in
      let t,ty = result_tuple ren'' (current_date ren) env
		   (Ident.result,CC_var Ident.result, CC_type) (eft,qt) in
      let t = make_let_in ren' ren'' env' te2 p2
		(current_vars ren'' (get_writes ef2),q2)
		(Ident.result,tv2) (t,ty) in
      let t = make_let_in ren ren' env te1 p1
     		(current_vars ren' (get_writes ef1),q1) (x,tv1) (t,ty) 
      in
      t

  | LetRec (f,bl,v,var,e) ->
      let c = match tt with Arrow(_,c) -> c | _ -> assert false in
      let (_,ef,_,_) = decomp_kappa c in
      let bl' = trad_binders ren env bl in
      let env' = traverse_binders env bl in
      let ren' = initial_renaming env' in
      let (phi0,var') = find_recursion f e.info.env in
      let te = trad ren' e in
      let t = make_letrec ren' env' (phi0,var') f bl' (te,e.info.kappa) c in
      CC_lam (bl', t)

  | Coerce e ->
      failwith "Mlize.trad: Coerce: todo"

  | PPoint (s,d) ->       
      let ren' = push_date ren s in
      trad_desc ren' env ct d

and trad_binders ren env = function
  | [] -> 
      []
  | (_,BindType (Ref _ | Array _)) :: bl ->
      trad_binders ren env bl
  | (id,BindType v) :: bl ->
      let tt = v (*i trad_ml_type_v ren env v i*) in
      (id, CC_var_binder tt) :: (trad_binders ren env bl)
  | (id,BindSet) :: bl ->
      assert false
      (*i (id, CC_typed_binder mkSet) :: (trad_binders ren env bl) i*)
  | (_,Untyped) :: _ -> 
      assert false
	
and trad_block ren env = function
  | [] -> 
      []
  | (Assert c) :: block ->
      (Assert c) :: (trad_block ren env block)
  | (Label s) :: block ->
      let ren' = push_date ren s in
      (Label s) :: (trad_block ren' env block)
  | (Statement e) :: block ->
      let te = trad ren e in
      let _,efe,_,_ = decomp_kappa e.info.kappa in
      let w = get_writes efe in
      let ren' = next ren w in
      (Statement (te,e.info.kappa)) :: (trad_block ren' env block)


and trans ren e =
  let env = e.info.env in
  let _,ef,p,_ = decomp_kappa e.info.kappa in
  let ty = trad_ml_type_c ren env e.info.kappa in
  let ids = get_reads ef in
  let al = current_vars ren ids in
  let c = trad ren e in
  let c = abs_pre ren env (c,ty) p in
  let bl = binding_of_alist ren env al in
  make_abs (List.rev bl) c

