(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: typing.ml,v 1.102 2003-12-18 13:31:36 marche Exp $ i*)

(*s Typing. *)

open Format
open Options
open Ident
open Misc
open Ltyping
open Util
open Logic
open Rename
open Types
open Ptree
open Error
open Report
open Ast
open Env 
open Effect
open Annot

(*s Typing of terms (used to type pure expressions). *)

let type_v_int = PureType PTint
let type_v_bool = PureType PTbool
let type_v_unit = PureType PTunit
let type_v_float = PureType PTfloat

let typing_const = function
  | ConstInt _ -> type_v_int
  | ConstBool _ -> type_v_bool
  | ConstUnit -> type_v_unit
  | ConstFloat _ -> type_v_float

(*s Utility functions for typing *)

let expected_cmp loc =
  raise_located loc 
    (ExpectedType (fun fmt -> fprintf fmt "unit, bool, int or float"))

let just_reads e = difference (get_reads e) (get_writes e)

let rec unify_type_v v1 v2 = 
  match (v1,v2) with
  | (PureType c1, PureType c2) -> 
      Ltyping.unify c1 c2
  | (Ref v1, Ref v2) -> 
      unify_type_v v1 v2
  | (Array v1, Array v2) -> 
      unify_type_v v1 v2
  | (Arrow(bl1,t1),Arrow(bl2,t2)) ->
      (List.length bl1 = List.length bl2)
      && (List.for_all2 
	    (fun (id1,b1) (id2,b2) ->
	       id1=id2 && 
	       match (b1,b2) with
		 | (BindType(t1),BindType(t2)) -> 
		     unify_type_v t1 t2
		 | (BindSet,BindSet) -> true
		 | _ -> false)	 
	    bl1 bl2)
      && unify_type_v t1.c_result_type t2.c_result_type			
  | _ -> false
(*
  | (v1,v2) -> 
      v1 = v2
*)

let type_v_sup loc t1 t2 =
  if not(unify_type_v t1 t2) then raise_located loc BranchesSameType;
  t1


let union3effects x y z = Effect.union x (Effect.union y z)

let decomp_fun_type f tf = match tf.info.kappa.c_result_type with
  | Arrow ([x,BindType v], k) ->
      x, v, k
  | Arrow ((x,BindType v) :: bl, k) ->
      x, v, type_c_of_v (Arrow (bl, k))
  | Arrow ((x,_) :: _, _) ->
      raise_located f.ploc (ExpectsATerm x)
  | Arrow ([], _) ->
      assert false
  | _ -> 
      raise_located f.ploc AppNonFunction

let expected_type loc t et =
  if not(unify_type_v t et) then 
    raise_located loc (ExpectedType (fun fmt -> print_type_v fmt et))

let check_for_alias loc id v = 
  if occur_type_v id v then raise_located loc (Alias id)

let check_for_let_ref loc v =
  if not (is_pure v) then raise_located loc Error.LetRef

let check_for_not_mutable loc v = 
  if is_mutable v then raise_located loc CannotBeMutable

let check_unbound_exn loc =
  let check (x,_) =
    if not (Env.is_exception x) then raise_located loc (UnboundException x)
  in
  List.iter check

(*s Instantiation of polymorphic functions *)

let type_prim idint idfloat idbool idunit loc = function
  | PureType PTint -> idint
  | PureType PTbool -> idbool
  | PureType PTfloat -> idfloat
  | PureType PTunit -> idunit
  | _ -> expected_cmp loc

let type_eq = type_prim t_eq_int t_eq_float t_eq_bool t_eq_unit
let type_neq = type_prim t_neq_int t_neq_float t_neq_bool t_neq_unit

let type_num idint idfloat loc = function
  | PureType PTint -> idint
  | PureType PTfloat -> idfloat
  | _ -> expected_num loc

let type_lt = type_num t_lt_int t_lt_float
let type_le = type_num t_le_int t_le_float
let type_gt = type_num t_gt_int t_gt_float
let type_ge = type_num t_ge_int t_ge_float
let type_add = type_num t_add_int t_add_float
let type_sub = type_num t_sub_int t_sub_float
let type_mul = type_num t_mul_int t_mul_float
let type_div = type_num t_div_int t_div_float
let type_neg = type_num t_neg_int t_neg_float

let type_poly id =
  if id == t_eq then type_eq 
  else if id == t_neq then type_neq
  else if id == t_lt then type_lt
  else if id == t_le then type_le 
  else if id == t_gt then type_gt
  else if id == t_ge then type_ge
  else if id == t_add then type_add 
  else if id == t_sub then type_sub
  else if id == t_mul then type_mul
  else if id == t_div then type_div
  else if id == t_neg then type_neg 
  else assert false

let type_un_poly id =
  if id == t_neg then type_neg else assert false

(*s Making nodes *)

let make_node loc p env l o k = 
  { desc = p; 
    info = { loc = loc; env = env; label = l; obligations = o; kappa = k } }

let make_arrow_type lab bl k =
  let k = 
    let q = optpost_app (change_label lab "") k.c_post in
    { k with c_post = q }
  in
  make_arrow bl k

let k_add_effects k e = { k with c_effect = Effect.union k.c_effect e }

(*s Typing variants. 
    Return the effect i.e. variables appearing in the variant. *)

let state_var lab env (phi,r) = 
  let lenv = logical_env env in
  let phi,tphi = Ltyping.term lab env lenv phi in
  let ids = term_refs env phi in
  (phi,tphi,r), Effect.add_reads ids Effect.bottom
	
(*s Typing preconditions.
    Return the effect i.e. variables appearing in the precondition. 
    Check existence of labels. *)

let predicates_effect lab env loc pl =
  let state e p =
    let ids = predicate_vars p in
    Idset.fold
      (fun id e ->
	 if is_reference env id then
	   Effect.add_read id e
	 else if is_at id then begin
	   let uid,l = un_at id in
	   if not (Label.mem l lab) then raise_located loc (UnboundLabel l);
	   if is_reference env uid then
	     Effect.add_read uid e
	   else
	     e
	 end else
	   e)
      ids e 
  in
  List.fold_left state Effect.bottom pl

let state_pre lab env loc pl =
  let lenv = logical_env env in
  let pl = List.map (type_assert lab env lenv) pl in
  predicates_effect lab env loc (List.map (fun x -> x.a_value) pl), pl

let state_assert lab env loc a =
  let a = type_assert lab env (logical_env env) a in
  predicates_effect lab env loc [a.a_value], a

let state_inv lab env loc = function
  | None -> 
      Effect.bottom, None
  | Some i -> 
      let i = type_assert lab env (logical_env env) i in
      predicates_effect lab env loc [i.a_value], Some i
	

(*s Typing postconditions.
    Return the effect i.e. variables appearing in the postcondition,
    together with the normalized postcondition (i.e. [x] replaced by [x@]
    whenever [x] is not modified by the program).
    Check existence of labels. *)

let state_post lab env (id,v,ef) loc = function
  | None -> 
      Effect.bottom, None
  | Some q ->
      check_unbound_exn loc (snd q);
      let q = type_post lab env (logical_env env) id v ef q in
      let ids = post_vars q in
      let ef,q = 
	Idset.fold
	  (fun id (e,q) ->
	     if is_reference env id then
	       if is_write ef id then
		 Effect.add_write id e, q
	       else
		 Effect.add_read id e,
		 post_app (subst_in_predicate (subst_onev id (at_id id ""))) q
	     else if is_at id then begin
	       let uid,l = un_at id in
	       if l <> "" && not (Label.mem l lab) then 
		 raise_located loc (UnboundLabel l);
	       if is_reference env uid then
		 Effect.add_read uid e, q
	       else
		 raise_located loc (UnboundReference uid)
	     end else
	       e,q)
	  ids (Effect.bottom, q)
      in
      ef, Some q

(*s Detection of pure functions. *)

let rec is_pure_type_v = function
  | PureType _ -> true
  | Arrow (bl,c) -> List.for_all is_pure_arg bl && is_pure_type_c c
  | Ref _ | Array _ -> false
and is_pure_arg = function
  | (_,BindType v) -> is_pure_type_v v
  | (_,BindSet) -> true
  | (_,Untyped) -> false
and is_pure_type_c c =
  is_pure_type_v c.c_result_type && c.c_effect = Effect.bottom &&
  c.c_pre = [] && c.c_post = None

(*s Preconditions for partial functions. *)

let partial_pre loc = function
  | Tapp (id, [a;b]) when id == t_div_int || id == t_mod_int ->
      let p = neq (unref_term b) (Tconst (ConstInt 0)) in
      [anonymous loc p]
  | Tapp (id, [a]) when id == t_sqrt_float ->
      let p = ge_float (unref_term a) (Tconst (ConstFloat "0.")) in
      [anonymous loc p]
  | _ ->
      []

(*s Types of references and arrays *)

let check_ref_type loc env id =
  try
    deref_type (type_in_env env id)
  with 
    | Not_found -> raise_located loc (UnboundReference id)
    | Invalid_argument _ -> raise_located loc (NotAReference id)
      
let check_array_type loc env id =
  try
    dearray_type (type_in_env env id)
  with 
    | Not_found -> raise_located loc (UnboundArray id)
    | Invalid_argument _ -> raise_located loc (NotAnArray id)
      
let check_no_effect loc ef =
  if not (Effect.get_writes ef = []) then raise_located loc HasSideEffects

(*s Saturation of postconditions: a postcondition must be set for
    any possibly raised exception *)

let warning_no_post loc x = 
  if not !c_file then begin
    wprintf loc "no postcondition for exception %a; false inserted@\n" 
      Ident.print x;
    if werror then exit 1
  end

let saturation loc e (a,al) =
  let xs = Effect.get_exns e in
  let check (x,_) =
    if not (List.mem x xs) then raise_located loc (CannotBeRaised x);
  in
  List.iter check al;
  let set_post x = 
    try 
      x, List.assoc x al 
    with Not_found -> 
      warning_no_post loc x;
      x, default_post 
  in
  (a, List.map set_post xs)

(*s The following flag indicates whether exceptions must be checked 
    as possibly raised in try-with constructs; indeed, this must be disabled
    when computing the effects of a recursive function. *)

let exn_check = ref true
let without_exn_check f x =
  if !exn_check then begin
    exn_check := false; 
    try let y = f x in exn_check := true; y 
    with e -> exn_check := true; raise e
  end else
    f x

(*s Typing programs. We infer here the type with effects. 
    [lab] is the set of labels, [env] the environment 
    and [expr] the program. *)

let rec typef lab env expr =
  let toplabel = label_name () in
  let lab = Label.add toplabel lab in
  let (d,(v,e),o1) = typef_desc lab env expr.ploc expr.pdesc in
  let loc = expr.ploc in
  let (ep,p) = state_pre lab env loc expr.pre in
  let (eo,o) = state_pre lab env loc expr.oblig in
  let (eq,q) = state_post lab env (result,v,e) loc expr.post in
  let q = option_app (saturation loc e) q in
  let e' = Effect.union e (Effect.union (Effect.union ep eo) eq) in
  let ol,q' = match q, d with
    | None, App (_,_,k') -> o @ o1 @ k'.c_pre, k'.c_post
    | _ -> o @ o1, q
  in
  let pr = 
    let c = { c_result_name = result; c_result_type = v; c_effect = e'; 
	      c_pre = p; c_post = q' } in
    make_node loc d env toplabel ol c
  in
  Annot.normalize pr

and typef_desc lab env loc = function
  | Sconst c ->
      Expression (Tconst c), (typing_const c, Effect.bottom), []

  | Svar id ->
      let v = 
	try type_in_env env id 
	with Not_found -> raise_located loc (UnboundVariable id)
      in
      let ef = Effect.bottom in
      if is_pure_type_v v && not (is_rec id env) then 
	Expression (Tvar id), (v,ef), []
      else 
	Var id, (v,ef), [] 

  | Srefget id ->
      let v = check_ref_type loc env id in
      let ef = Effect.add_read id Effect.bottom in
      Expression (Tderef id), (v,ef), []

  | Srefset (x, e1) ->
      let et = check_ref_type loc env x in
      let t_e1 = typef lab env e1 in
      expected_type e1.ploc (result_type t_e1) et;
      let e = t_e1.info.kappa.c_effect in
      let ef = add_write x e in
      let v = type_v_unit in
      Aff (x, t_e1), (v,ef), []

  | Sarrget (check, x, e) ->
      let t_e = typef lab env e in
      expected_type e.ploc (result_type t_e) type_v_int;
      let efe = t_e.info.kappa.c_effect in
      let ef = Effect.add_read x efe in
      let ty = check_array_type loc env x in
      let s,p = match t_e.desc with
	| Expression c when post t_e = None ->
	    let t = make_raw_access env (x,x) c in
	    let pre = anonymous loc (make_pre_access env x c) in
	    Expression t, t_e.info.obligations @ [pre]
	| _ ->
	    (* turned into [let v = e in x[v]] *)
	    let v = fresh_var () in
	    let env' = Env.add v type_v_int env in
	    let varv = make_var loc v type_v_int env' in
	    let pre = anonymous loc (make_pre_access env x (Tvar v)) in
	    let k = k_add_effects (type_c_of_v ty) (add_read x bottom) in
	    LetIn (v, t_e,
		   make_lnode loc (TabAcc (check, x, varv)) env' [pre] k), []
      in
      s, (ty, ef), p

  | Sarrset (check, x, e1, e2) ->
      let t_e1 = typef lab env e1 in
      expected_type e1.ploc (result_type t_e1) type_v_int;
      let t_e2 = typef lab env e2 in 
      let et = check_array_type loc env x in
      expected_type e2.ploc (result_type t_e2) et;
      let ef1 = t_e1.info.kappa.c_effect in
      let ef2 = t_e2.info.kappa.c_effect in
      let ef = Effect.add_write x (Effect.union ef1 ef2) in
      let v = type_v_unit in
      let d,p = match t_e1.desc, post t_e1, t_e2.desc, post t_e2 with
	| Expression ce1, None, Expression _, None ->
	    (* simple enough to be left as is *)
	    let pre = anonymous loc (make_pre_access env x ce1) in
	    TabAff (check, x, t_e1, t_e2), [pre]
	| _ ->
	    (* turned into [let v2 = e2 in let v1 = e1 in x[v1] := v2] *)
	    let v1 = fresh_var () in
	    let v2 = fresh_var () in
	    let env2 = Env.add v2 et env in
	    let env1 = Env.add v1 type_v_int env2 in
	    let varv1 = make_var loc v1 type_v_int env2 in
	    let varv2 = make_var loc v2 et env2 in
	    let pre1 = anonymous loc (make_pre_access env x (Tvar v1)) in
	    let k = type_c_of_v type_v_unit in
	    let k0 = k_add_effects k (add_write x bottom) in
	    let k1 = k_add_effects k0 ef1 in
	    LetIn (v2, t_e2,
		   make_lnode loc
		     (LetIn (v1, t_e1,
			     make_lnode loc (TabAff (check, x, varv1, varv2))
			       env1 [pre1] k0)) 
		     env2 [] k1),
	    []
      in
      d, (v,ef), p

  | Sseq bl ->
      let bl,v,ef = typef_block lab env bl in
      Seq bl, (v,ef), []
	      
  | Swhile (b, invopt, var, e) ->
      let var,efphi = state_var lab env var in
      let t_b = typef lab env b in
      let efb = t_b.info.kappa.c_effect in
      let t_e = typef lab env e in
      let efe = t_e.info.kappa.c_effect in
      let efinv,invopt = state_inv lab env loc invopt in
      let ef = 
	Effect.union (Effect.union efe efb) (Effect.union efinv efphi)
      in
      let v = type_v_unit in
      While (t_b,invopt,var,t_e), (v,ef), []
      
  | Slam ([], _) ->
      assert false

  | Slam (bl, e) ->
      let bl',env',_ = binders loc lab env (logical_env env) bl in
      let t_e = typef lab env' e in
      check_for_not_mutable e.ploc t_e.info.kappa.c_result_type;
      let v = make_arrow_type t_e.info.label bl' t_e.info.kappa in
      let ef = Effect.bottom in
      Lam (bl',t_e), (v,ef), []

  | Sapp ({pdesc=Svar id} as e, Sterm a) when is_poly id ->
      let t_a = typef lab env a in
      let eq = type_poly id a.ploc (result_type t_a) in
      typef_desc lab env loc (Sapp ({e with pdesc = Svar eq}, Sterm a))
      (* TODO: avoid recursive call? *)

  | Sapp ({pdesc=Svar id}, Sterm a) when id == Ident.array_length ->
       let t_a = typef lab env a in
       (match result_type t_a, t_a.desc with
	  | Array _, Var t -> 
	      let ef = Effect.add_read t Effect.bottom in
	      Expression (array_length t), (type_v_int, ef), []
	  | _ -> 
	      raise_located a.ploc (AnyMessage "array expected"))

  | Sapp (f, Sterm a) ->
      let t_f = typef lab env f in
      let x,tx,kapp = decomp_fun_type f t_f in
      let kapp = force_type_c_loc loc kapp in
      let t_a = typef lab env a in
      expected_type a.ploc (result_type t_a) tx;
      (match tx with 
      (* the function expects a mutable; it must be a variable *)
      | Ref _ | Array _ -> (match t_a with
	  | { desc = Var r } ->
	      check_for_alias a.ploc r (result_type t_f);
	      let kapp = type_c_subst (subst_onev x r) kapp in
	      let (_,tapp),eapp,_,_ = decomp_kappa kapp in
	      let ef = Effect.union (effect t_f) eapp in
	      App (t_f, Refarg r, kapp), (tapp, ef), []
	  | _ ->
	      raise_located a.ploc ShouldBeVariable)
      (* argument is not mutable *)
      | _ ->
	  let (_,tapp),eapp,_,_ = decomp_kappa kapp in
	  let ef = union3effects (effect t_a) (effect t_f) eapp in
	  (match t_a.desc with
  	     (* argument is pure: it is substituted *)
	     | Expression ca when post t_a = None ->
		 (* let tca = put_label_term env "" (unref_term ca) in *)
		 let kapp = type_c_subst_oldify env x ca kapp in
		 let (_,tapp),_,_,_ = decomp_kappa kapp in
		 (match t_f.desc with
		    (* function itself is pure: we collapse terms *)
		    | Expression cf when post t_f = None ->
			let e = applist cf [ca] in
			let pl = partial_pre loc e @ preo t_a @ preo t_f in
			Expression e, (tapp, ef), pl
 		    (* function is [let y = ty in E]: we lift this let *)
		    | LetIn (y, ty, ({ desc = Expression cf } as tf'))
		      when post tf' = None && post t_f = None ->
			let e = applist cf [ca] in
			let env' = tf'.info.env in
			let pl = 
			  partial_pre loc e @ preo tf' @ preo t_a @ preo t_f 
			in
			LetIn (y, ty, 
			       make_lnode loc (Expression e) env' [] kapp),
			(tapp, ef), pl
	            (* otherwise: true application *)
		    | _ ->	   
			(* TODO: check [t_f] without effect *)
			let pl = preo t_f @ preo t_a in
			App (t_f, Term t_a, kapp), (tapp, ef), pl)
	     (* argument is complex: 
		we transform into [let v = arg in (f v)] *)
	     | _ ->
		 if occur_type_v x tapp then 
		   raise_located a.ploc TooComplexArgument;
		 let v = fresh_var () in
		 let kapp = type_c_subst (subst_onev x v) kapp in
		 let env' = Env.add v tx env in
		 let app_f_v,pl = match t_f.desc with
		   (* function is pure: we collapse terms *)
		   | Expression cf when post t_f = None ->
		       let e = applist cf [Tvar v] in
		       Expression e, partial_pre loc e @ preo t_f
		   (* function is [let y = ty in E]: we lift this let *)
		   | LetIn (y, ty, ({ desc = Expression cf } as tf')) 
		     when post tf' = None && post t_f = None ->
		       let e = applist cf [Tvar v] in
		       let env'' = Env.add v tx tf'.info.env in
		       LetIn (y, ty, 
			      make_lnode loc (Expression e) env'' [] kapp),
		       partial_pre loc e @ preo tf' @ preo t_f
	           (* otherwise: true application *)
		   | _ ->
		       let var_v = make_var loc v tx env' in
		       App (t_f, Term var_v, kapp), []
		 in
		 let kfv = k_add_effects kapp (effect t_f) in
		 LetIn (v, t_a, make_lnode loc app_f_v env' [] kfv), 
		 (tapp, ef), pl))

  | Sapp (f, Stype _) ->
      failwith "todo: typing: application to a type"
      
  | Sletref (x, e1, e2) ->
      if is_ref env x then raise_located loc (ClashRef x);
      let t_e1 = typef lab env e1 in
      let ef1 = t_e1.info.kappa.c_effect in
      let v1 = t_e1.info.kappa.c_result_type in
      let env' = add x (Ref v1) env in
      let t_e2 = typef lab env' e2 in
      let ef2 = t_e2.info.kappa.c_effect in
      let v2 = t_e2.info.kappa.c_result_type in
      check_for_let_ref loc v2;
      let ef = Effect.union ef1 (Effect.remove x ef2) in
      LetRef (x, t_e1, t_e2), (v2,ef), []
	
  | Sletin (x, e1, e2) ->
      let t_e1 = typef lab env e1 in
      let ef1 = t_e1.info.kappa.c_effect in
      let v1 = t_e1.info.kappa.c_result_type in
      check_for_not_mutable e1.ploc v1;
      let env' = add x v1 env in
      let t_e2 = typef lab env' e2 in
      let ef2 = t_e2.info.kappa.c_effect in
      let v2 = t_e2.info.kappa.c_result_type in
      let ef = Effect.union ef1 ef2 in
      LetIn (x, t_e1, t_e2), (v2,ef), []
	    
  | Sif (b, e1, e2) ->
      let t_b = typef lab env b in
      expected_type b.ploc (result_type t_b) type_v_bool;
      let t_e1 = typef lab env e1
      and t_e2 = typef lab env e2 in
      let t1 = t_e1.info.kappa.c_result_type in
      let t2 = t_e2.info.kappa.c_result_type in
      let ef = union3effects (effect t_b) (effect t_e1) (effect t_e2) in
      let v = type_v_sup loc t1 t2 in
      If (t_b, t_e1, t_e2), (v,ef), []

  | Srec (f,bl,v,var,e) ->
      let bl',env',lenv' = binders loc lab env (logical_env env) bl in
      let v = type_v loc lab env' lenv' v in
      let var,efvar = state_var lab env' var in
      let phi0 = phi_name () in
      (* effects for a let/rec construct are computed as a fixpoint *)
      let type_body c =
	let tf = make_arrow bl' c in
	let env'' = add_rec f (add f tf env') in
	typef lab env'' e
      in
      let fixpoint_reached c1 c2 =
	c1.c_effect = c2.c_effect && 
        List.length c1.c_pre = List.length c2.c_pre &&
        (match c1.c_post, c2.c_post with 
         | None, None | Some _, Some _ -> true | _ -> false)
      in
      let rec fixpoint c =
	let t_e = type_body c in
	if fixpoint_reached t_e.info.kappa c then
	  t_e
      	else begin
	  if_debug_3 eprintf "  (rec => %a)@\n@?" print_type_c t_e.info.kappa;
	  fixpoint t_e.info.kappa
      	end
      in 
      let c0 = { c_result_name = result; c_result_type = v;
		 c_effect = efvar; c_pre = []; c_post = None } in
      let t_e = without_exn_check fixpoint c0 in (* fixpoint, without check *)
      let t_e = type_body t_e.info.kappa in (* once again, with checks *)
      let tf = make_arrow bl' t_e.info.kappa in
      Rec (f,bl',v,var,t_e), (tf,Effect.bottom), []

  | Sraise (id, e, ct) ->
      if not (is_exception id) then raise_located loc (UnboundException id);
      let t_e, ef = match find_exception id , e with
	| None, Some _ -> 
	    raise_located loc (ExceptionArgument (id, false))
	| Some _, None ->
	    raise_located loc (ExceptionArgument (id, true))
	| Some xt, Some e ->
	    let t_e = typef lab env e in
	    expected_type e.ploc (result_type t_e) (PureType xt);
	    Some t_e, effect t_e
	| None, None -> 
	    None, Effect.bottom
      in
      let v = match ct with 
	| None -> type_v_unit 
	| Some v -> type_v loc lab env (logical_env env) v
      in
      Raise (id, t_e), (v, Effect.add_exn id ef), []

  | Stry (e, hl) ->
      let te = typef lab env e in
      let v = result_type te in
      let ef = effect te in
      let xs = get_exns ef in
      let ef = List.fold_left (fun e ((x,_),_) -> remove_exn x e) ef hl in
      let type_handler ((x,a),h) =
	if not (is_exception x) then raise_located loc (UnboundException x);
	if not (List.mem x xs) && !exn_check then 
	  raise_located e.ploc (CannotBeRaised x);
	let env' = match a, find_exception x with 
	  | None, None -> env 
	  | Some v, Some tv -> Env.add v (PureType tv) env
	  | None, Some _ -> raise_located loc (ExceptionArgument (x, true))
	  | Some _, None -> raise_located loc (ExceptionArgument (x, false))
	in
	let th = typef lab env' h in
	expected_type h.ploc (result_type th) v;
	((x,a), th)
      in
      let thl = List.map type_handler hl in
      let ef = List.fold_left (fun e (_,th) -> union e (effect th)) ef thl in
      Try (te, thl), (v, ef), []

  | Sabsurd ct -> 	    
      let v = match ct with 
	| None -> type_v_unit 
	| Some v -> type_v loc lab env (logical_env env) v
      in
      Absurd, (v, Effect.bottom), [anonymous loc Pfalse]

and typef_block lab env bl =
  let rec ef_block lab tyres = function
    | [] ->
	begin match tyres with
	  | Some (ty,_) -> [], ty, Effect.bottom
	  | None -> assert false
	end
    | (Sassert c) :: block -> 
	let ep,p = state_assert lab env c.a_value.pp_loc c in
	let bl,t,ef = ef_block lab tyres block in
	(Assert p)::bl, t, Effect.union ep ef
    | (Slabel s) :: block ->
	let lab' = Label.add s lab in
	let bl,t,ef = ef_block lab' tyres block in
	(Label s)::bl, t, ef
    | (Sstatement e) :: block ->
	option_iter (fun (t,l) -> expected_type l t type_v_unit) tyres;
	let t_e = typef lab env e in
	let efe = t_e.info.kappa.c_effect in
	let t = t_e.info.kappa.c_result_type in
	let bl,t,ef = ef_block lab (Some (t,e.ploc)) block in
	(Statement t_e)::bl, t, Effect.union efe ef
  in
  ef_block lab None bl

