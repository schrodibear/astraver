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

(*i $Id: ltyping.ml,v 1.41 2006-01-18 09:40:41 filliatr Exp $ i*)

(*s Typing on the logical side *)

open Format
open Options
open Ident
open Logic
open Types
open Ptree
open Ast
open Misc
open Util
open Env
open Error
open Report

let expected_num loc =
  raise_located loc (ExpectedType (fun fmt -> fprintf fmt "int or real"))

let expected_type loc et =
  raise_located loc (ExpectedType (fun fmt -> print_type_v fmt et))

let rec pure_type = function
  | PPTint -> PTint
  | PPTbool -> PTbool
  | PPTreal -> PTreal
  | PPTunit -> PTunit
  | PPTvar x -> PTvar x
  | PPTvarid (x, _) -> PTvarid x
  | PPTexternal (p, id, loc) ->
      if not (is_type id) then raise_located loc (UnboundType id);
      let np = List.length p in
      let a = type_arity id in
      if np <> a then raise_located loc (TypeArity (id, a, np));
      PTexternal (List.map pure_type p, id)

(*s Typing predicates *)

let int_cmp = function
  | PPlt -> t_lt_int
  | PPle -> t_le_int
  | PPgt -> t_gt_int
  | PPge -> t_ge_int
  | PPeq -> t_eq_int
  | PPneq -> t_neq_int
  | _ -> assert false

let real_cmp = function
  | PPlt -> t_lt_real
  | PPle -> t_le_real
  | PPgt -> t_gt_real
  | PPge -> t_ge_real
  | PPeq -> t_eq_real
  | PPneq -> t_neq_real
  | _ -> assert false

let other_cmp = function
  | PTbool, PPeq -> t_eq_bool
  | PTbool, PPneq -> t_neq_bool
  | PTunit, PPeq -> t_eq_unit
  | PTunit, PPneq -> t_neq_unit
  | _, PPeq -> t_eq
  | _, PPneq -> t_neq
  | _ -> assert false


let rec unify t1 t2 = match (t1,t2) with
  (* instantiable variables *)
  | (PTvar v1, _) ->
      begin
	match v1.type_val with
	  | None -> v1.type_val <- Some t2; true
	  | Some ta -> unify ta t2
      end
  | (_, PTvar v2) ->
      begin
	match v2.type_val with 
	  | None -> v2.type_val <- Some t1; true
	  | Some tb -> unify t1 tb
      end
  (* recursive types *)
  | (PTexternal(l1,i1), PTexternal(l2,i2)) ->
      i1 = i2 && List.length l1 = List.length l2 &&
      List.for_all2 unify l1 l2
  | (PTexternal _), _
  | _, (PTexternal _) ->
      false
  (* other cases *)
  | (PTvarid xa, PTvarid xb) -> xa = xb
  | (PTvarid _, _)
  | (_, PTvarid _) -> 
      false
  | (PTunit | PTreal | PTbool | PTint), _ -> 
      t1 = t2

let make_comparison loc = function
  | (a,PTint), (PPlt|PPle|PPgt|PPge|PPeq|PPneq as r), (b,PTint) ->
      Papp (int_cmp r, [a; b], [])
  | (a,PTreal), (PPlt|PPle|PPgt|PPge|PPeq|PPneq as r), (b,PTreal) ->
      Papp (real_cmp r, [a; b], [])
  | (a,ta), r, (b,tb) ->
      if unify ta tb then
	match normalize_pure_type ta, normalize_pure_type tb with
	  | PTint, PTint -> Papp (int_cmp r, [a;b], [])
	  | PTreal, PTreal -> Papp (real_cmp r, [a;b], [])
	  | _ -> Papp (other_cmp (ta,r), [a; b], [])
      else
	raise_located loc 
	  (ExpectedType (fun f -> Util.print_pure_type f (normalize_pure_type tb)))

let int_arith = function
  | PPadd -> t_add_int
  | PPsub -> t_sub_int
  | PPmul -> t_mul_int
  | PPdiv -> t_div_int
  | PPmod -> t_mod_int
  | _ -> assert false

let real_arith = function
  | PPadd -> t_add_real
  | PPsub -> t_sub_real
  | PPmul -> t_mul_real
  | PPdiv -> t_div_real
  | _ -> assert false

let make_arith loc = function
  | (a,PTint), (PPadd|PPsub|PPmul|PPdiv|PPmod as r), (b,PTint) ->
      Tapp (int_arith r, [a; b], []), PTint
  | (a,PTreal), (PPadd|PPsub|PPmul|PPdiv as r), (b,PTreal) ->
      Tapp (real_arith r, [a; b], []), PTreal
  | _ ->
      expected_num loc

let predicate_expected loc =
  raise_located loc (AnyMessage "syntax error: predicate expected")

let term_expected loc =
  raise_located loc (AnyMessage "syntax error: term expected")

(* Table of closed instances *)

module Instances = 
  Set.Make(struct type t = pure_type list let compare = compare end)

let instances_t = Hashtbl.create 97

let instances x = 
  try Hashtbl.find instances_t x with Not_found -> Instances.empty

let add_instance x i =
  let s = try Hashtbl.find instances_t x with Not_found -> Instances.empty in
  Hashtbl.replace instances_t x (Instances.add i s)

let add_instance_if_closed x i = 
  try 
    let ci = 
      List.map (fun pt -> if is_closed_pure_type pt then pt else raise Exit) i
    in
    add_instance x ci
  with Exit -> 
    ()

let instance x i = 
  let i = 
    List.map (fun v -> match v.type_val with None -> PTvar v | Some pt -> pt) i
  in 
  add_instance_if_closed x i; i

let iter_instances f = Hashtbl.iter (fun x -> Instances.iter (f x)) instances_t

(* typing predicates *)

let rec predicate lab env lenv p =
  desc_predicate p.pp_loc lab env lenv p.pp_desc

and desc_predicate loc lab env lenv = function
  | PPvar x ->
      type_pvar loc lenv x
  | PPapp (x, pl) ->
      type_papp loc lenv x (List.map (term lab env lenv) pl)
  | PPtrue ->
      Ptrue
  | PPfalse ->
      Pfalse
  | PPconst _ ->
      predicate_expected loc
  | PPinfix (a, PPand, b) ->
      Pand (false, true, predicate lab env lenv a, predicate lab env lenv b)
  | PPinfix (a, PPiff, b) ->
      Piff (predicate lab env lenv a, predicate lab env lenv b)
  | PPinfix (a, PPor, b) ->
      Por (predicate lab env lenv a, predicate lab env lenv b)
  | PPinfix (a, PPimplies, b) ->
      Pimplies (false, predicate lab env lenv a, predicate lab env lenv b)
  | PPinfix 
      ({pp_desc = PPinfix (_, (PPlt|PPle|PPgt|PPge|PPeq|PPneq), a)} as p, 
       (PPlt | PPle | PPgt | PPge | PPeq | PPneq as r), b) ->
      let q = { pp_desc = PPinfix (a, r, b); pp_loc = loc } in
      Pand (false, true, predicate lab env lenv p, predicate lab env lenv q)
  | PPinfix (a, (PPlt | PPle | PPgt | PPge | PPeq | PPneq as r), b) ->
      make_comparison a.pp_loc (term lab env lenv a, r, term lab env lenv b)
  | PPinfix (_, (PPadd | PPsub | PPmul | PPdiv | PPmod), _) -> 
      predicate_expected loc
  | PPprefix (PPneg, _) ->
      predicate_expected loc
  | PPprefix (PPnot, a) ->
      Pnot (predicate lab env lenv a)
  | PPif (a, b, c) ->
      (match term lab env lenv a with
	 | ta, PTbool -> 
	     Pif (ta, predicate lab env lenv b, predicate lab env lenv c)
	 | _ -> 
	     raise_located a.pp_loc ShouldBeBoolean)
  | PPforall (id, pt, a) ->
      let v = PureType (pure_type pt) in
      forall id v 
	(predicate lab env (Env.add_logic ~generalize:false id v lenv) a)
  | PPexists (id, pt, a) ->
      let v = PureType (pure_type pt) in
      exists id v (predicate lab env (Env.add_logic id v lenv) a)
  | PPfpi (e, f1, f2) ->
      (match term lab env lenv e with
	 | te, PTreal -> Pfpi (te, f1, f2)
	 | _ -> raise_located e.pp_loc 
	         (AnyMessage "this expression should have type real"))
  | PPnamed (n, a) ->
      Pnamed (n, predicate lab env lenv a)

and type_pvar loc lenv x =
  if is_at x then 
    raise_located loc (AnyMessage "predicates cannot be labelled");
  if not (is_logic x lenv) then raise_located loc (UnboundVariable x);
  match snd (find_logic x lenv) with
    | Predicate [] -> Pvar x
    | Function _ -> predicate_expected loc
    | _ -> raise_located loc PartialApp

and type_papp loc lenv x tl =
  if not (is_logic x lenv) then raise_located loc (UnboundVariable x);
  match find_logic x lenv with
    | vars, Predicate at -> 
	check_type_args loc at tl; 
	Papp (x, List.map fst tl, instance x vars)
    | _ -> 
	predicate_expected loc

and term lab env lenv t =
  desc_term t.pp_loc lab env lenv t.pp_desc

and desc_term loc lab env lenv = function
  | PPvar x ->
      type_tvar loc lab env lenv x
  | PPapp (id, [a; b; c]) when id == if_then_else ->
      type_if lab env lenv a b c
  | PPif (a, b, c) ->
      type_if lab env lenv a b c
  | PPapp (x, tl) ->
      let tl = List.map (term lab env lenv) tl in
      let ty, i = type_tapp loc lenv x tl in
      Tapp (x, List.map fst tl, i), ty
  | PPtrue ->
      ttrue, PTbool
  | PPfalse ->
      tfalse, PTbool
  | PPconst c ->
      Tconst c, type_const c
  | PPinfix (a, (PPadd|PPsub|PPmul|PPdiv|PPmod as r), b) ->
      make_arith loc (term lab env lenv a, r, term lab env lenv b)
  | PPinfix (_, (PPand|PPor|PPiff|PPimplies
		|PPlt|PPle|PPgt|PPge|PPeq|PPneq), _) ->
      term_expected loc
  | PPprefix (PPneg, a) ->
      (match term lab env lenv a with
	 | ta, PTint -> Tapp (t_neg_int, [ta], []), PTint
	 | ta, PTreal -> Tapp (t_neg_real, [ta], []), PTreal
	 | _ -> expected_num loc)
  | PPprefix (PPnot, _) | PPforall _ | PPexists _ | PPfpi _ | PPnamed _ ->
      term_expected loc

and type_if lab env lenv a b c =
  match term lab env lenv a, term lab env lenv b, term lab env lenv c with
    | (ta, PTbool), (tb, tyb), (tc, tyc) -> 
	if tyb <> tyc then 
	  raise_located c.pp_loc 
	    (ExpectedType (fun f -> print_pure_type f tyb));
	Tapp (if_then_else, [ta; tb; tc], []), tyb
    | _ -> raise_located a.pp_loc ShouldBeBoolean

and type_tvar loc lab env lenv x = 
  let xu = 
    if is_at x then begin
      let xu,l = un_at x in
      if not (is_reference env xu) then raise_located loc (NotAReference xu);
      if not (Label.mem l lab) then raise_located loc (UnboundLabel l);
      xu
    end else 
      x
  in
  if not (is_logic xu lenv) then raise_located loc (UnboundVariable xu);
  match snd (find_logic xu lenv) with
    | Function ([], t) -> Tvar x, t
    | _ -> raise_located loc (MustBePure)

and type_tapp loc lenv x tl =
  if not (is_logic x lenv) then raise_located loc (UnboundVariable x);
  match find_logic x lenv with
    | vars, Function (at, t) -> 
	check_type_args loc at tl; t, instance x vars
    | _ -> 
	raise_located loc (AppNonFunction)

and check_type_args loc at tl =
  let rec check_arg = function
    | [], [] -> 
	()
    | a :: al, (tb,b) :: bl ->
	if unify a b then
	  check_arg (al, bl)
	else
	  raise_located loc (TermExpectedType ((fun f -> print_term f tb),
					       fun f -> print_pure_type f a))
    | [], _ ->
	raise_located loc TooManyArguments
    | _, [] ->
	raise_located loc PartialApp
  in
  check_arg (at, tl)

and type_const = function
  | ConstInt _ -> PTint
  | ConstBool _ -> PTbool
  | ConstUnit -> PTunit
  | ConstFloat _ -> PTreal


(*s Checking types *)

let type_assert ?(namer=h_name) lab env lenv a = 
  { a_value = predicate lab env lenv a.pa_value;
    a_name = namer a.pa_name;
    a_loc = a.pa_loc;
    a_proof = None }

let type_post lab env lenv id v ef (a,al) = 
  let lab' = Label.add "" lab in 
  let a' = 
    let lenv' = Env.add_logic id v lenv in type_assert lab' env lenv' a 
  in
  let xs = Effect.get_exns ef in
  let check_exn (x,a) =
    let loc = a.pa_value.pp_loc in
    if not (is_exception x) then raise_located loc (UnboundException x);
    if not (List.mem x xs) then raise_located loc (CannotBeRaised x)
  in
  List.iter check_exn al;
  let loc = a.pa_value.pp_loc in
  let type_exn_post x =
    try
      let a = List.assoc x al in
      let lenv' = match find_exception x with
	| None -> lenv
	| Some pt -> Env.add_logic result (PureType pt) lenv
      in
      (x, type_assert lab' env lenv' a)
    with Not_found ->
      wprintf loc "no postcondition for exception %a; false inserted@\n"
	Ident.print x;
      (x, anonymous loc Pfalse)
  in
  (a', List.map type_exn_post xs)

let check_effect loc env e =
  let check_ref id =
    if not (Env.is_ref env id) then raise_located loc (UnboundReference id)
  in
  let check_exn id =
    if not (Env.is_exception id) then raise_located loc (UnboundException id)
  in
  let r,w,x = Effect.get_repr e in
  List.iter check_ref r;
  List.iter check_ref w;
  List.iter check_exn x

(* warns if a ref occuring in a predicate is not mentioned in the effect,
   and adds it as read to the effect *)
let warn_refs loc env p = 
  Idset.fold 
    (fun id ef -> 
       if not (Effect.is_read ef id) then begin
	 wprintf loc "mutable %a is not declared in effect; added as read\n"
	   Ident.print id;
	 if werror then exit 1;
	 Effect.add_read id ef
       end else
	 ef)
    (predicate_refs env p)

let effect e =
  List.fold_right Effect.add_write e.pe_writes
    (List.fold_right Effect.add_read e.pe_reads
       (List.fold_right Effect.add_exn e.pe_raises Effect.bottom))

let rec type_v loc lab env lenv = function
  | PVpure pt -> 
      PureType (pure_type pt)
  | PVref v -> 
      Ref (pure_type v)
  | PVarrow (bl, c) -> 
      let bl',env',lenv' = binders loc lab env lenv bl in 
      make_arrow bl' (type_c loc lab env' lenv' c)

and pure_type_v loc lab env lenv = function
  | PVpure pt ->
      PureType (pure_type pt)
  | _ ->
      raise_located loc MutableMutable

and type_c loc lab env lenv c =
  let ef = effect c.pc_effect in
  check_effect loc env ef;
  let v = type_v loc lab env lenv c.pc_result_type in
  let id = c.pc_result_name in
  let p = List.map (type_assert lab env lenv) c.pc_pre in
  let q = option_app (type_post lab env lenv id v ef) c.pc_post in
  let ef = List.fold_right (asst_fold (warn_refs loc env)) p ef in
  let ef = optpost_fold (warn_refs loc env) q ef in
  let s = subst_onev id Ident.result in
  let p = List.map (fun a -> a.a_value) p in
  let q = optpost_app (fun a -> subst_in_predicate s a.a_value) q in
  { c_result_name = c.pc_result_name; c_effect = ef;
    c_result_type = v; c_pre = p; c_post = q }

and binders loc lab env lenv = function
  | [] ->
      [], env, lenv
  | (id, v) :: bl ->
      let v = type_v loc lab env lenv v in
      let bl',env',lenv' = 
	binders loc lab (Env.add id v env) 
	  (Env.add_logic ~generalize:false id v lenv) bl 
      in
      (id, v) :: bl', env', lenv'

let logic_type = function
  | PPredicate pl -> Predicate (List.map pure_type pl)
  | PFunction (pl, t) -> Function (List.map pure_type pl, pure_type t)

