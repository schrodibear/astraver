(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: ltyping.ml,v 1.2 2002-07-08 09:02:28 filliatr Exp $ i*)

(*s Typing on the logical side *)

open Format
open Ident
open Logic
open Types
open Ptree
open Misc
open Util
open Env

let expected_cmp loc =
  Error.expected_type loc (fun fmt -> fprintf fmt "unit, bool, int or float")

let expected_num loc =
  Error.expected_type loc (fun fmt -> fprintf fmt "int or float")

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
  | _ -> assert false

let make_comparison loc = function
  | (a,PTint), (PPlt|PPle|PPgt|PPge|PPeq|PPneq as r), (b,PTint) ->
      Papp (int_cmp r, [a; b])
  | (a,PTfloat), (PPlt|PPle|PPgt|PPge|PPeq|PPneq as r), (b,PTfloat) ->
      Papp (float_cmp r, [a; b])
  | (a,(PTbool|PTunit as ta)), (PPeq | PPneq as r), (b,(PTbool|PTunit as tb))
    when ta = tb ->
      Papp (other_cmp (ta,r), [a; b])
  | _ ->
      expected_cmp loc

let int_arith = function
  | PPadd -> t_add_int
  | PPsub -> t_sub_int
  | PPmul -> t_mul_int
  | PPdiv -> t_div_int
  | PPmod -> t_mod
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
      Tapp (float_cmp r, [a; b]), PTfloat
  | _ ->
      expected_num loc

let check_label loc lab =
  if_labelled 
    (fun (_,l) -> 
       if not (LabelSet.mem l lab) then Error.unbound_label l (Some loc))

let predicate_expected loc =
  raise (Stdpp.Exc_located (loc, Stream.Error "predicate expected"))

let term_expected loc =
  raise (Stdpp.Exc_located (loc, Stream.Error "term expected"))

let rec predicate lab lenv p =
  desc_predicate p.pp_loc lab lenv p.pp_desc

and desc_predicate loc lab lenv = function
  | PPvar x ->
      type_pvar loc lenv x
  | PPapp (x, pl) ->
      type_papp loc lenv x (List.map (term lab lenv) pl)
  | PPtrue ->
      Ptrue
  | PPfalse ->
      Pfalse
  | PPconst _ ->
      predicate_expected loc
  | PPinfix (a, PPand, b) ->
      Pand (predicate lab lenv a, predicate lab lenv b)
  | PPinfix (a, PPor, b) ->
      Por (predicate lab lenv a, predicate lab lenv b)
  | PPinfix (a, PPimplies, b) ->
      Pimplies (predicate lab lenv a, predicate lab lenv b)
  | PPinfix (a, (PPlt | PPle | PPgt | PPge | PPeq | PPneq as r), b) ->
      make_comparison loc (term lab lenv a, r, term lab lenv b)
  | PPinfix (_, (PPadd | PPsub | PPmul | PPdiv | PPmod), _) -> 
      predicate_expected loc
  | PPprefix (PPneg, _) ->
      predicate_expected loc
  | PPprefix (PPnot, a) ->
      Pnot (predicate lab lenv a)
  | PPif (a, b, c) ->
      (match term lab lenv a with
	 | ta, PTbool -> Pif (ta, predicate lab lenv b, predicate lab lenv c)
	 | _ -> Error.should_be_boolean a.pp_loc)
  | PPforall (id, pt, a) ->
      let v = PureType pt in
      forall id v (predicate lab (Env.add_logic id v lenv) a)

and type_pvar loc lenv x =
  if not (is_logic x lenv) then Error.unbound_variable x (Some loc);
  match find_logic x lenv with
    | Predicate [] -> Pvar x
    | Function _ -> predicate_expected loc
    | _ -> Error.partial_app loc

and type_papp loc lenv x tl =
  if not (is_logic x lenv) then Error.unbound_variable x (Some loc);
  match find_logic x lenv with
    | Predicate at -> check_type_args loc at tl; Papp (x, List.map fst tl)
    | _ -> predicate_expected loc

and term lab lenv t =
  desc_term t.pp_loc lab lenv t.pp_desc

and desc_term loc lab lenv = function
  | PPvar x ->
      check_label loc lab x;
      Tvar x, type_tvar loc lenv x
  | PPapp (x, [a;b]) when x == Ident.access ->
      (match term lab lenv a, term lab lenv b with
	 | (a, PTarray (_,v)), (b, PTint) ->
	     Tapp (x, [a;b]), v
	 | (Tvar t,_), _ ->
	     Error.unbound_array t (Some a.pp_loc)
	 | _ ->
	     assert false)
  | PPapp (x, tl) ->
      let tl = List.map (term lab lenv) tl in
      Tapp (x, List.map fst tl), type_tapp loc lenv x tl
  | PPtrue ->
      ttrue, PTbool
  | PPfalse ->
      tfalse, PTbool
  | PPconst c ->
      Tconst c, type_const c
  | PPinfix (a, (PPadd|PPsub|PPmul|PPdiv|PPmod as r), b) ->
      make_arith loc (term lab lenv a, r, term lab lenv b)
  | PPinfix (_, (PPand|PPor|PPimplies|PPlt|PPle|PPgt|PPge|PPeq|PPneq), _) ->
      term_expected loc
  | PPprefix (PPneg, a) ->
      (match term lab lenv a with
	 | ta, PTint -> Tapp (t_neg_int, [ta]), PTint
	 | ta, PTfloat -> Tapp (t_neg_float, [ta]), PTfloat
	 | _ -> expected_num loc)
  | PPprefix (PPnot, _) | PPif _ | PPforall _ ->
      term_expected loc

and type_tvar loc lenv x = 
  let x = if is_at x then fst (un_at x) else x in
  if not (is_logic x lenv) then Error.unbound_variable x (Some loc);
  match find_logic x lenv with
    | Function ([], t) -> t
    | _ -> Error.must_be_pure loc

and type_tapp loc lenv x tl =
  if not (is_logic x lenv) then Error.unbound_variable x (Some loc);
  match find_logic x lenv with
    | Function (at, t) -> check_type_args loc at tl; t
    | _ -> Error.app_of_non_function loc

and check_type_args loc at tl =
  let rec check_arg = function
    | [], [] -> 
	()
    | a :: al, (tb,b) :: bl ->
	if a <> b then
	  Error.term_expected_type loc 
	    (fun f -> print_term f tb) (fun f -> print_pure_type f a); 
	check_arg (al, bl)
    | [], _ ->
	Error.too_many_arguments loc
    | _, [] ->
	Error.partial_app loc
  in
  check_arg (at, tl)

and type_const = function
  | ConstInt _ -> PTint
  | ConstBool _ -> PTbool
  | ConstUnit -> PTunit
  | ConstFloat _ -> PTfloat


(*s Checking types *)

let type_pre lab lenv p = { p with p_value = predicate lab lenv p.p_value }

let type_post lab lenv a = 
  let lab' = LabelSet.add "" lab in 
  { a with a_value = predicate lab' lenv a.a_value }

let check_effect loc env e =
  let check_ref id =
    if not (Env.is_ref env id) then Error.unbound_reference id loc
  in
  let check_exn id =
    if not (Env.is_exception id) then Error.unbound_exception id loc
  in
  let r,w,x = Effect.get_repr e in
  List.iter check_ref r;
  List.iter check_ref w;
  List.iter check_exn x

let rec type_v loc lab env lenv = function
  | PVref v -> 
      Ref (type_v loc lab env lenv v)
  | PVarray (t, v) -> 
      let t,_ = term lab lenv t in
      Array (t, type_v loc lab env lenv v)
  | PVarrow (bl, c) -> 
      let bl',env',lenv' = binders loc lab env lenv bl in 
      make_arrow bl' (type_c loc lab env' lenv' c)
  | PVpure pt -> 
      PureType pt

and type_c loc lab env lenv c =
  check_effect loc env c.pc_effect;
  let v = type_v loc lab env lenv c.pc_result_type in
  let id = c.pc_result_name in
  let p = List.map (type_pre lab lenv) c.pc_pre in
  let lenv' = Env.add_logic id v lenv in
  let q = option_app (type_post lab lenv') c.pc_post in
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
