(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: mlize.ml,v 1.18 2002-03-13 10:35:30 filliatr Exp $ i*)

open Ident
open Logic
open Misc
open Types
open Ast
open Util
open Rename
open Env
open Effect
open Monad

(*s Translation of imperative programs into functional ones.
    [ren] is the current renamings of variables,
    [e] is the imperative program to translate, annotated with type+effects.
    We return the translated program in type [cc_term] *)

let rec trad e =
  cross_label e.info.label (trad_desc e.info e.desc)

and trad_desc info d ren = match d with
  | Expression t ->
      Monad.unit info t ren

  | Var id ->
      assert (not (is_reference info.env id));
      if is_local info.env id then
	CC_var id
      else
	CC_expr (Tvar id)

  | Acc _ ->
      assert false

  | Aff (x, e1) ->
      Monad.compose 
	e1.info (trad e1)
	(fun res1 ren' -> 
	   let t1 = trad_ml_type_v ren info.env (result_type e1) in
	   let ren'' = next ren' [x] in
	   let x' = current_var ren'' x in
	   CC_letin (false, [x', CC_var_binder t1], CC_expr (Tvar res1), 
		     Monad.unit info (Tconst ConstUnit) ren''))
	ren

  | Seq bl ->
      trad_block info bl ren

  | If (b, e1, e2) ->
      Monad.compose b.info (trad b)
	(fun resb ren' -> 
	   let branch e tb = 
	     let t = 
	       Monad.compose e.info (trad e) 
		 (fun r -> Monad.unit info (Tvar r)) ren'
	     in
	     match post b with
	       | Some qb -> 
		   let n = test_name Anonymous in
		   let q = apply_post ren' info.env qb in
		   let q = tsubst_in_predicate [result, tb] q.a_value in
		   CC_lam ([n, CC_pred_binder q], t)
	       | None -> t
	   in
	   CC_if (CC_var resb, branch e1 ttrue, branch e2 tfalse))
	ren

  | Coerce e ->
      Monad.compose e.info (trad e) (fun res -> Monad.unit info (Tvar res)) ren

  | App (e1, Term e2) ->
      Monad.compose e2.info (trad e2)
	(fun v2 -> 
	   Monad.compose e1.info (trad e1)
	     (fun v1 -> 
		Monad.compose info (fun _ -> CC_app (CC_var v1, [CC_var v2]))
		  (fun v -> Monad.unit info (Tvar v))))
	ren

  | LetIn (x, e1, e2) ->
      Monad.compose e1.info (trad e1)
	(fun v1 ren' ->
	   let t1 = trad_ml_type_v ren info.env (result_type e1) in
	   CC_letin (false, [x, CC_var_binder t1], CC_expr (Tvar v1), 
		     Monad.compose e2.info (trad e2) 
		       (fun v2 -> Monad.unit info (Tvar v2)) ren'))
	ren

  | _ -> failwith "Mlize.trad: TODO"

(*i***
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
****i*)

and trad_block info =
  let rec block res = function
    | [] -> 
	(match res with
	   | Some id -> Monad.unit info (Tvar id)
	   | None -> assert false)
    | (Assert c) :: bl ->
	let p = 
	  { p_assert = true; p_name = c.a_name; p_value = c.a_value } 
	in
	insert_pre info.env p (block res bl)
    | (Label s) :: bl ->
	cross_label s (block res bl)
    | (Statement e) :: bl ->
	Monad.compose e.info (trad e) (fun x -> block (Some x) bl)
  in
  block None

and trans e =
  cross_label e.info.label (abstraction e.info.env e.info.kappa (trad e))

