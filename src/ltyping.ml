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

(*i $Id: ltyping.ml,v 1.17 2003-02-05 08:14:11 filliatr Exp $ i*)

(*s Typing on the logical side *)

open Format
open Ident
open Logic
open Types
open Ptree
open Misc
open Util
open Env
open Error
open Report

let expected_num loc =
  raise_located loc (ExpectedType (fun fmt -> fprintf fmt "int or float"))

let expected_type loc et =
  raise_located loc (ExpectedType (fun fmt -> print_type_v fmt et))

(*s Typing predicates *)

let int_cmp = function
  | PPlt -> t_lt_int
  | PPle -> t_le_int
  | PPgt -> t_gt_int
  | PPge -> t_ge_int
  | PPeq -> t_eq_int
  | PPneq -> t_neq_int
  | _ -> assert false

let float_cmp = function
  | PPlt -> t_lt_float
  | PPle -> t_le_float
  | PPgt -> t_gt_float
  | PPge -> t_ge_float
  | PPeq -> t_eq_float
  | PPneq -> t_neq_float
  | _ -> assert false

let other_cmp = function
  | PTbool, PPeq -> t_eq_bool
  | PTbool, PPneq -> t_neq_bool
  | PTunit, PPeq -> t_eq_unit
  | PTunit, PPneq -> t_neq_unit
  | _, PPeq -> t_eq
  | _, PPneq -> t_neq
  | _ -> assert false

let make_comparison loc = function
  | (a,PTint), (PPlt|PPle|PPgt|PPge|PPeq|PPneq as r), (b,PTint) ->
      Papp (int_cmp r, [a; b])
  | (a,PTfloat), (PPlt|PPle|PPgt|PPge|PPeq|PPneq as r), (b,PTfloat) ->
      Papp (float_cmp r, [a; b])
  | (a,ta), (PPeq | PPneq as r), (b,tb) when ta = tb ->
      Papp (other_cmp (ta,r), [a; b])
  | _, _, (_,tb) ->
      raise_located loc (ExpectedType (fun f -> Util.print_pure_type f tb))

let int_arith = function
  | PPadd -> t_add_int
  | PPsub -> t_sub_int
  | PPmul -> t_mul_int
  | PPdiv -> t_div_int
  | PPmod -> t_mod_int
  | _ -> assert false

let float_arith = function
  | PPadd -> t_add_float
  | PPsub -> t_sub_float
  | PPmul -> t_mul_float
  | PPdiv -> t_div_float
  | _ -> assert false

let make_arith loc = function
  | (a,PTint), (PPadd|PPsub|PPmul|PPdiv|PPmod as r), (b,PTint) ->
      Tapp (int_arith r, [a; b]), PTint
  | (a,PTfloat), (PPadd|PPsub|PPmul|PPdiv as r), (b,PTfloat) ->
      Tapp (float_arith r, [a; b]), PTfloat
  | _ ->
      expected_num loc

let check_label loc lab env =
  if_labelled 
    (fun (id,l) -> 
       if not (is_reference env id) then raise_located loc (NotAReference id);
       if not (LabelSet.mem l lab) then raise_located loc (UnboundLabel l))

let predicate_expected loc =
  raise (Stdpp.Exc_located (loc, Stream.Error "predicate expected"))

let term_expected loc =
  raise (Stdpp.Exc_located (loc, Stream.Error "term expected"))

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
      Pand (predicate lab env lenv a, predicate lab env lenv b)
  | PPinfix (a, PPor, b) ->
      Por (predicate lab env lenv a, predicate lab env lenv b)
  | PPinfix (a, PPimplies, b) ->
      Pimplies (predicate lab env lenv a, predicate lab env lenv b)
  | PPinfix (a, (PPlt | PPle | PPgt | PPge | PPeq | PPneq as r), b) ->
      make_comparison loc (term lab env lenv a, r, term lab env lenv b)
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
      let v = PureType pt in
      forall id v (predicate lab env (Env.add_logic id v lenv) a)
  | PPexists (id, pt, a) ->
      let v = PureType pt in
      exists id v (predicate lab env (Env.add_logic id v lenv) a)

and type_pvar loc lenv x =
  if is_at x then 
    raise_located loc (AnyMessage "predicates cannot be labelled");
  if not (is_logic x lenv) then raise_located loc (UnboundVariable x);
  match find_logic x lenv with
    | Predicate [] -> Pvar x
    | Function _ -> predicate_expected loc
    | _ -> raise_located loc PartialApp

and type_papp loc lenv x tl =
  if not (is_logic x lenv) then raise_located loc (UnboundVariable x);
  match find_logic x lenv with
    | Predicate at -> check_type_args loc at tl; Papp (x, List.map fst tl)
    | _ -> predicate_expected loc

and term lab env lenv t =
  desc_term t.pp_loc lab env lenv t.pp_desc

and desc_term loc lab env lenv = function
  | PPvar x ->
      Tvar x, type_tvar loc lab env lenv x
  | PPapp (x, [a;b]) when x == Ident.access ->
      (match term lab env lenv a, term lab env lenv b with
	 | (a, PTarray v), (b, PTint) ->
	     Tapp (x, [a;b]), v
	 | (_, PTarray _), _ ->
	     expected_type b.pp_loc (PureType PTint)
	 | (Tvar t,_), _ ->
	     raise_located a.pp_loc (UnboundArray t)
	 | _ ->
	     assert false)
  | PPapp (x, [a]) when x == Ident.array_length ->
      (match term lab env lenv a with
	 | a, PTarray _ -> Tapp (x, [a]), PTint
	 | Tvar t, _ -> raise_located a.pp_loc (UnboundArray t)
	 | _ -> raise_located a.pp_loc (AnyMessage "array expected"))
  | PPapp (id, [a; b; c]) when id == if_then_else ->
      type_if lab env lenv a b c
  | PPif (a, b, c) ->
      type_if lab env lenv a b c
  | PPapp (x, tl) ->
      let tl = List.map (term lab env lenv) tl in
      Tapp (x, List.map fst tl), type_tapp loc lenv x tl
  | PPtrue ->
      ttrue, PTbool
  | PPfalse ->
      tfalse, PTbool
  | PPconst c ->
      Tconst c, type_const c
  | PPinfix (a, (PPadd|PPsub|PPmul|PPdiv|PPmod as r), b) ->
      make_arith loc (term lab env lenv a, r, term lab env lenv b)
  | PPinfix (_, (PPand|PPor|PPimplies|PPlt|PPle|PPgt|PPge|PPeq|PPneq), _) ->
      term_expected loc
  | PPprefix (PPneg, a) ->
      (match term lab env lenv a with
	 | ta, PTint -> Tapp (t_neg_int, [ta]), PTint
	 | ta, PTfloat -> Tapp (t_neg_float, [ta]), PTfloat
	 | _ -> expected_num loc)
  | PPprefix (PPnot, _) | PPforall _ | PPexists _ ->
      term_expected loc

and type_if lab env lenv a b c =
  match term lab env lenv a, term lab env lenv b, term lab env lenv c with
    | (ta, PTbool), (tb, tyb), (tc, tyc) -> 
	if tyb <> tyc then 
	  raise_located c.pp_loc 
	    (ExpectedType (fun f -> print_pure_type f tyb));
	Tapp (if_then_else, [ta; tb; tc]), tyb
    | _ -> raise_located a.pp_loc ShouldBeBoolean

and type_tvar loc lab env lenv x = 
  let xu = if is_at x then fst (un_at x) else x in
  if not (is_logic xu lenv) then raise_located loc (UnboundVariable xu);
  check_label loc lab env x;
  match find_logic xu lenv with
    | Function ([], t) -> t
    | _ -> raise_located loc (MustBePure)

and type_tapp loc lenv x tl =
  if not (is_logic x lenv) then raise_located loc (UnboundVariable x);
  match find_logic x lenv with
    | Function (at, t) -> check_type_args loc at tl; t
    | _ -> raise_located loc (AppNonFunction)

and check_type_args loc at tl =
  let illtyped a b = match a, b with
    | PTarray a, PTarray b -> a <> b
    | _ -> a <> b
  in
  let rec check_arg = function
    | [], [] -> 
	()
    | a :: al, (tb,b) :: bl ->
	if illtyped a b then
	  raise_located loc (TermExpectedType ((fun f -> print_term f tb),
					       fun f -> print_pure_type f a)); 
	check_arg (al, bl)
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
  | ConstFloat _ -> PTfloat


(*s Checking types *)

let type_assert lab env lenv a = 
  { a with a_value = predicate lab env lenv a.a_value }

let type_post lab env lenv id v ef (a,al) = 
  let lab' = LabelSet.add "" lab in 
  let a' = 
    let lenv' = Env.add_logic id v lenv in type_assert lab' env lenv' a 
  in
  let xs = Effect.get_exns ef in
  let type_exn_post (x,a) =
    let loc = a.a_value.pp_loc in
    if not (is_exception x) then raise_located loc (UnboundException x);
    if not (List.mem x xs) then raise_located loc (CannotBeRaised x);
    let lenv' = match find_exception x with
      | None -> lenv
      | Some pt -> Env.add_logic result (PureType pt) lenv
    in
    (x, type_assert lab' env lenv' a)
  in
  (a', List.map type_exn_post al)

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

let rec type_v loc lab env lenv = function
  | PVref v -> 
      Ref (type_v loc lab env lenv v)
  | PVarray v -> 
      Array (type_v loc lab env lenv v)
  | PVarrow (bl, c) -> 
      let bl',env',lenv' = binders loc lab env lenv bl in 
      make_arrow bl' (type_c loc lab env' lenv' c)
  | PVpure pt -> 
      PureType pt

and type_c loc lab env lenv c =
  check_effect loc env c.pc_effect;
  let v = type_v loc lab env lenv c.pc_result_type in
  let id = c.pc_result_name in
  let p = List.map (type_assert lab env lenv) c.pc_pre in
  let q = option_app (type_post lab env lenv id v c.pc_effect) c.pc_post in
  let s = subst_onev id Ident.result in
  let q = optpost_app (subst_in_predicate s) q in
  { c_result_name = c.pc_result_name; c_effect = c.pc_effect;
    c_result_type = v; c_pre = p; c_post = q }

and binders loc lab env lenv = function
  | [] ->
      [], env, lenv
  | (id, BindType v) :: bl ->
      let v = type_v loc lab env lenv v in
      let bl',env',lenv' = 
	binders loc lab (Env.add id v env) (Env.add_logic id v lenv) bl 
      in
      (id, BindType v) :: bl', env', lenv'
  | (id, BindSet) :: bl ->
      let bl',env',lenv' = binders loc lab (Env.add_set id env) lenv bl in
      (id, BindSet) :: bl', env', lenv'
  | (id, Untyped) :: bl ->
      let bl',env',lenv' = binders loc lab env lenv bl in
      (id, Untyped) :: bl', env', lenv'
