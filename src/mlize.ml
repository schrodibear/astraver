(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(*i $Id: mlize.ml,v 1.51 2002-09-06 11:45:20 filliatr Exp $ i*)

open Ident
open Logic
open Misc
open Types
open Ast
open Util
open Rename
open Env
open Monad

let make_info env k = { env = env; label = label_name (); kappa = k }

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
      if is_rec id then
	find_rec id ren 
      else
	CC_var id

  | Acc _ ->
      assert false

  | Aff (x, e1) ->
      Monad.compose 
	e1.info (trad e1)
	(fun res1 ren' -> 
	   let tx = trad_type_in_env ren info.env x in
	   let ren'' = next ren' [x] in
	   let x' = current_var ren'' x in
	   CC_letin (false, [x', CC_var_binder tx], CC_var res1, 
		     Monad.unit info (Tconst ConstUnit) ren''))
	ren

  | Seq bl ->
      trad_block info bl ren

  | If (e1, e2, e3) ->
      trad_conditional info 
	e1.info (trad e1) e2.info (trad e2) e3.info (trad e3) 
	ren

  | LetIn (x, e1, e2) ->
      let k1 = { e1.info.kappa with c_result_name = x } in
      let info1 = { e1.info with kappa = k1 } in
      Monad.compose info1 (trad e1)
	(fun v1 ren' ->
	   let te2 = 
	     Monad.compose e2.info (trad e2) 
	       (fun v2 -> Monad.unit info (Tvar v2)) ren' 
	   in
	   if v1 <> x then
	     let ty1 = trad_type_v ren info.env (result_type e1) in
	     CC_letin (false, [x, CC_var_binder ty1], CC_var v1, te2)
	   else
	     te2)
	ren

  | LetRef (x, e1, e2) ->
      Monad.compose e1.info (trad e1)
	(fun v1 ren' ->
	   let t1 = trad_type_v ren info.env (result_type e1) in
	   let ren'' = next ren' [x] in
	   let x' = current_var ren'' x in
	   CC_letin (false, [x', CC_var_binder t1], CC_var v1, 
		     Monad.compose e2.info (trad e2)
		       (fun v2 -> Monad.unit info (Tvar v2)) ren''))
	ren

  | Coerce e ->
      Monad.compose e.info (trad e) (fun res -> Monad.unit info (Tvar res)) ren

  | App (e1, Term e2, kapp) ->
      let infoapp = make_info info.env kapp in
      Monad.compose e2.info (trad e2)
	(fun v2 -> 
	   Monad.compose e1.info (trad e1)
	     (fun v1 -> 
		Monad.apply infoapp 
		  (fun _ -> CC_app (CC_var v1, CC_var v2))
		  (fun v -> Monad.unit info (Tvar v))))
	ren

  | App (e1, Refarg r, kapp) ->
      let infoapp = make_info info.env kapp in
      Monad.compose e1.info (trad e1)
	(fun v1 -> 
	   Monad.apply infoapp (fun _ -> CC_var v1)
	     (fun v -> Monad.unit info (Tvar v)))
	ren

  | App (_, Type _, _) ->
      failwith "Mlize.trad: App Type"

  | Lam (bl, e) ->
      let bl',env' = trad_binders ren info.env bl in
      let ren' = initial_renaming env' in
      let te = trans e ren' in
      cc_lam bl' te

  | TabAcc (_, x, e1) ->
      Monad.compose e1.info (trad e1)
	(fun v1 ren' -> 
	   let x' = current_var ren' x in
	   let t = make_raw_access info.env (x,x') (Tvar v1) in
	   let p = anonymous_pre true (make_pre_access info.env x (Tvar v1)) in
	   insert_pre info.env p (Monad.unit info t) ren')
	ren

  | TabAff (_, x, e1, e2) ->
       Monad.compose e2.info (trad e2)
	 (fun v2 -> 
	    Monad.compose e1.info (trad e1)
	      (fun v1 ren' -> 
		 let tx = trad_type_in_env ren info.env x in
		 let x' = current_var ren' x in
		 let ren'' = next ren' [x] in
  		 let x'' = current_var ren'' x in
		 let st = make_raw_store info.env (x,x') (Tvar v1) (Tvar v2) in
		 let p = make_pre_access info.env x (Tvar v1) in
		 CC_letin (false, [x'', CC_var_binder tx], CC_term st,
			   insert_pre info.env (anonymous_pre true p)
			     (Monad.unit info (Tconst ConstUnit)) ren'')))
	 ren

  | While (b, inv, var, e) ->
      let info' = 
	let p = 
	  match inv with Some a -> [pre_of_assert false a] | None -> [] 
	in
	{ info with kappa = { info.kappa with c_pre = p }}
      in
      let infoc = make_info info.env info.kappa in
      Monad.wfrec var info'
	(fun w -> 
	   let exit = Monad.unit info (Tconst ConstUnit) in
	   let loop = Monad.compose e.info (trad e) (fun _ -> w) in
	   trad_conditional infoc b.info (trad b) infoc loop infoc exit)
	ren

  | Rec (f, bl, v, var, e) -> 
      let bl',env' = trad_binders ren info.env bl in
      let ren' = push_date (initial_renaming env') e.info.label in
      let recf w ren = cc_lam bl' (abstraction e.info w ren) in
      cc_lam bl' 
	(abstraction e.info 
	   (Monad.wfrec_with_binders bl' var e.info
	      (fun w -> with_rec f (recf w) (trad e)))
	   ren')

  | Raise (id, None) ->
      Monad.exn info id None ren

  | Raise (id, Some e) ->
      Monad.compose e.info (trad e) 
	(fun v -> Monad.exn info id (Some (Tvar v))) 
	ren

and trad_binders ren env = function
  | [] -> 
      [], env
  | (id, BindType (Ref _ | Array _ as v)) :: bl ->
      trad_binders ren (Env.add id v env) bl
  | (id, BindType v) :: bl ->
      let tt =  trad_type_v ren env v in
      let env' = Env.add id v env in
      let bl',env'' = trad_binders ren env' bl in
      (id, CC_var_binder tt) :: bl', env''
  | (_, (BindSet | Untyped)) :: _ ->
      assert false

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

(* to be used for both [if] and [while] *)
and trad_conditional info info1 te1 info2 te2 info3 te3 =
  Monad.compose info1 te1
    (fun resb ren' -> 
       let q1 = 
	 option_app (apply_post info1.label ren' info.env) info1.kappa.c_post
       in
       let branch infob eb tb = 
	 let t = 
	   Monad.compose infob eb (fun r -> Monad.unit info (Tvar r)) ren'
	 in
	 match q1 with
	   | Some q -> 
	       let n = test_name Anonymous in
	       let q = tsubst_in_predicate (subst_one result tb) q.a_value in
	       CC_lam ((n, CC_pred_binder (simplify q)), t)
	   | None -> 
	       t
       in
       CC_if (CC_var resb,  
	      branch info2 te2 ttrue, branch info3 te3 tfalse))

and trans e =
  cross_label e.info.label (abstraction e.info (trad e))

