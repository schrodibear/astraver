(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
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

(*i $Id: cltyping.ml,v 1.68 2004-12-08 14:17:29 hubert Exp $ i*)

open Cast
open Clogic
open Creport
open Cerror
open Cenv
open Ctypes

let option_app f = function Some x -> Some (f x) | None -> None

(* Typing terms *)

(*
let noattr tyn = { ctype_node = tyn; 
		   ctype_storage = No_storage;
		   ctype_const = false;
		   ctype_volatile = false }
let c_void = noattr CTvoid
let c_int = noattr (CTint (Signed, Int))
let c_char = noattr (CTint (Unsigned, Char))
let c_float = noattr (CTfloat Float)
let c_string = noattr (CTpointer c_char)
let c_array ty = noattr (CTarray (ty, None))
let c_array_size ty s = noattr (CTarray (ty, Some s))
let c_pointer ty = noattr (CTpointer ty)
let c_void_star = c_pointer c_void
let c_addr = noattr (CTvar "addr")
*)

let is_null t = match t.term_node with
  | Tnull -> true
  | Tconstant (IntConstant s) -> (try int_of_string s = 0 with _ -> false)
  | _ -> false

let compatible t1 t2 = 
  sub_type t1.term_type t2.term_type || 
  sub_type t2.term_type t1.term_type ||
  (pointer_or_array_type t1.term_type && is_null t2) ||
  (pointer_or_array_type t2.term_type && is_null t1)

let compatible_term_type t ty = 
  sub_type t.term_type ty || 
  sub_type ty t.term_type ||
  (pointer_or_array_type ty && is_null t)

let expected_type loc t1 t2 =
  if not (eq_type t1 t2) then raise_located loc (ExpectedType (t1, t2))

let expected_term_type loc t1 t2 =
  if not (compatible_term_type t1 t2) 
  then raise_located loc (ExpectedType (t1.term_type, t2))

let expected_num loc t = match t.term_type.ctype_node with
  | Tenum _ | Tint _ | Tfloat _ -> ()
  | _ -> error loc "invalid operand (expected integer or float)"

let expected_num_pointer loc t = match t.term_type.ctype_node with
  | Tenum _ | Tint _ | Tfloat _ 
  | Tarray _ | Tpointer _ -> ()
  | _ -> 
      Format.eprintf "type = %a@." print_type t.term_type;
      error loc "invalid operand (expected integer, float or pointer)"

let expected_int loc t = match t.term_type.ctype_node with
  | Tint _ -> ()
  | _ -> error loc "invalid operand (expected integer)"

let max_type t1 t2 = match t1.ctype_node, t2.ctype_node with
  | Tint _, Tint _ -> c_int
  | Tint _, Tfloat _
  | Tfloat _, Tint _
  | Tfloat _, Tfloat _ -> c_float
  | _ -> assert false

(* Typing terms *)

open Info

let rec type_term env t =
  let t', ty = type_term_node t.lexpr_loc env t.lexpr_node in
  { term_node = t'; term_loc = t.lexpr_loc; term_type = ty }

and type_term_node loc env = function
  | PLconstant (IntConstant _ as c) -> 
      Tconstant c, c_int
  | PLconstant (FloatConstant _ as c) ->
      Tconstant c, c_float
  | PLvar x ->
      let info = 
	try Env.find x.var_name env with Not_found -> 
	try find_sym x.var_name with Not_found -> 
        error loc ("unbound variable " ^ x.var_name)
      in 
      begin match info with
	| Var_info v -> Clogic.Tvar v, v.var_type
	| Fun_info f -> 
            error loc ("variable " ^ f.fun_name ^ " is a function")
      end
  | PLapp (f, tl) ->
      (try 
	 let pl, ty, info = find_fun f.logic_name in
	 let tl = type_terms loc env pl tl in
	 Tapp (info, tl), ty
       with Not_found -> 
	 error loc ("unbound function " ^ f.logic_name))
  | PLunop (Utilde, t) -> 
      let t = type_int_term env t in
      Tunop (Utilde, t), t.term_type
  | PLunop (Uminus, t) -> 
      let t = type_num_term env t in
      Tunop (Uminus, t), t.term_type
  | PLunop (Ustar, t) -> 
      let t = type_term env t in
      begin match t.term_type.ctype_node with
	| Tpointer ty | Tarray (ty,_) -> Tunop (Ustar, t), ty
	| _ -> error loc "invalid type argument of `unary *'"
      end
  | PLunop (Uamp, t) -> 
      let t = type_term env t in
      Tunop (Uamp, t), noattr (Tpointer t.term_type)
  | PLunop ((Ufloat_of_int | Uint_of_float), _) ->
      assert false
  | PLbinop (t1, Badd, t2) ->
      let t1 = type_term env t1 in
      let ty1 = t1.term_type in
      let t2 = type_term env t2 in
      let ty2 = t2.term_type in
      begin match ty1.ctype_node, ty2.ctype_node with
	| (Tenum _ | Tint _ | Tfloat _), (Tenum _ | Tint _ | Tfloat _) ->
	    Tbinop (t1, Badd, t2), max_type ty1 ty2
	| (Tpointer _ | Tarray _), (Tint _ | Tenum _) -> 
	    Tbinop (t1, Badd, t2), ty1
	| (Tenum _ | Tint _), (Tpointer _ | Tarray _) ->
	    Tbinop (t2, Badd, t1), ty2
	| _ -> 
	    error loc "invalid operands to binary +"
      end
  | PLbinop (t1, Bsub, t2) ->
      let t1 = type_term env t1 in
      let ty1 = t1.term_type in
      let t2 = type_term env t2 in
      let ty2 = t2.term_type in
      begin match ty1.ctype_node, ty2.ctype_node with
	| (Tenum _ | Tint _ | Tfloat _), (Tenum _ | Tint _ | Tfloat _) ->
	    Tbinop (t1, Bsub, t2), max_type ty1 ty2
	| (Tpointer _ | Tarray _), (Tint _ | Tenum _) -> 
	    let mt2 = { term_node = Tunop (Uminus, t2); 
			term_loc = t2.term_loc;
			term_type = ty2 } in
	    Tbinop (t1, Badd, mt2), ty1
	| (Tpointer _ | Tarray _), (Tpointer _ | Tarray _) ->
	    Tbinop (t1, Bsub, t2), ty1 (* TODO check types *)
	| _ -> error loc "invalid operands to binary -"
      end
  | PLbinop (t1, (Bmul | Bdiv as op), t2) ->
      let t1 = type_num_term env t1 in
      let t2 = type_num_term env t2 in
      Tbinop (t1, op, t2), max_type t1.term_type t2.term_type
  | PLbinop (t1, Bmod, t2) ->
      let t1 = type_int_term env t1 in
      let t2 = type_int_term env t2 in
      Tbinop (t1, Bmod, t2), c_int
  | PLdot (t, x) ->
      let t = type_term env t in
      let x = type_of_field loc x t.term_type in
      let t_dot_x = match t.term_node with
	| Tunop (Ustar, e) -> 
	    Tarrow (e, x)
	| Tarrget (e1, e2) -> 
	    let a = 
	      { term_node = Tbinop (e1, Badd, e2); 
		term_loc = t.term_loc;
		term_type = e1.term_type }
	    in
	    Tarrow (a, x)
	| _ -> 
	    Tdot (t, x)
      in
      t_dot_x, x.var_type
  | PLarrow (t, x) ->
      let t = type_term env t in
      begin match t.term_type.ctype_node with
	| Tpointer ty -> 
	    let x = type_of_field loc x ty in
	    Tarrow (t, x), x.var_type
	| _ -> 
	    error loc "invalid type argument of `->'"
      end
  | PLarrget (t1, t2) ->
      let t1 = type_term env t1 in
      (match t1.term_type.ctype_node with
	 | Tarray (ty,_) | Tpointer ty ->
	     let t2 = type_int_term env t2 in
	     Tarrget (t1, t2), ty
	 | _ ->
	     error loc "subscripted value is neither array nor pointer")
  | PLif (t1, t2, t3) ->
      (* TODO type de t1 ? *)
      unsupported loc "logic if-then-else"
  | PLold t ->
      let t = type_term env t in
      Told t, t.term_type
  | PLat (t, l) ->
      (* TODO check label l *)
      let t = type_term env t in
      Tat (t, l), t.term_type
  | PLbase_addr t ->
      let t = type_term env t in
      (match t.term_type.ctype_node with
	 | Tarray _ | Tpointer _ -> Tbase_addr t, c_addr
	 | _ -> error loc "subscripted value is neither array nor pointer")
  | PLblock_length t ->
      let t = type_term env t in
      (match t.term_type.ctype_node with
	 | Tarray _ | Tpointer _ -> Tblock_length t, c_int
	 | _ -> error loc "subscripted value is neither array nor pointer")
  | PLresult ->
      (try let t = Env.find "\\result" env in Tresult, (var_type t)
       with Not_found -> error loc "\\result meaningless")
  | PLnull ->
      Tnull, c_void_star
  | PLcast (ty, t) ->
      let t = type_term env t in
      let tt = t.term_type in
      begin match ty, tt.ctype_node with
	| LTvoid, Tvoid
	| LTint, Tint _ 
	| LTfloat, Tfloat _ -> t.term_node, tt
	| LTfloat, Tint _ -> Tunop (Ufloat_of_int, t), c_float
	| LTint, Tfloat _ -> Tunop (Uint_of_float, t), c_int
	| _ -> warning loc "ignored cast in annotation"; t.term_node, tt
      end
  | PLvalid _ | PLvalid_index _ | PLvalid_range _ | PLfresh _ 
  | PLexists _ | PLforall _ | PLnot _ | PLimplies _ | PLiff _
  | PLor _ | PLand _ | PLrel _ | PLtrue | PLfalse | PLnamed _ ->
      raise_located loc (AnyMessage "syntax error")

and type_int_term env t =
  let tt = type_term env t in
  expected_int t.lexpr_loc tt;
  tt

and type_num_term env t =
  let tt = type_term env t in
  expected_num t.lexpr_loc tt;
  tt

and type_num_pointer_term env t =
  let tt = type_term env t in
  expected_num_pointer t.lexpr_loc tt;
  tt

and type_terms loc env at tl =
  let rec type_list = function
    | [], [] -> 
	[]
    | et :: etl, ({lexpr_loc=tloc} as t) :: tl ->
	let t = type_term env t in
	expected_term_type tloc t et;
	t :: type_list (etl, tl)
    | [], _ ->
	raise_located loc TooManyArguments
    | _, [] ->
	raise_located loc PartialApp
  in
  type_list (at, tl)

(* Typing logic types *)

let rec type_type env t = 
  { t with ctype_node = type_type_node env t.ctype_node }

and type_type_node env = function
  | Tint _ | Tfloat _ as t -> t
  | Tarray (ty,t) -> Tarray (type_type env ty,t)
  | _ -> assert false

let rec type_logic_type env = function
  | LTvoid -> c_void
  | LTint -> c_int
  | LTfloat -> c_float
  | LTarray ty -> c_array (type_logic_type env ty)
  | LTpointer ty -> c_pointer (type_logic_type env ty)
  | LTvar id ->  
      noattr (try (find_typedef id).ctype_node with Not_found -> Tvar id)

(** abandon provisoire 
let rec type_logic_type env = function
  | PTctype ct ->
      PTctype (type_type env ct)
  | PTvar {tag=n; type_val =t } -> 
      PTvar { tag = n; type_val = option_app (type_logic_type env) t }
  | PTexternal (tl, s) -> 
      PTexternal (List.map (type_logic_type env) tl, s)
**)

(*
let type_quantifier env (ty, x) = (type_logic_type env ty, x)
let type_quantifiers env = List.map (type_quantifier env)
*)

let add_quantifiers q env =
  let (tq,env) =
    List.fold_left
      (fun (tq,env) (ty, x) -> 
	 let i = Info.default_var_info x 
	 and ty = type_logic_type env ty
	 in
	 ((ty,i)::tq,Env.add x ty (Var_info i) env))
      ([],env) q
  in
  (List.rev tq,env)


let int_constant n = 
  { term_node = Tconstant (IntConstant n); 
    term_loc = Loc.dummy;
    term_type = c_int }

let zero = int_constant "0"

(* Typing predicates *)

let rec type_predicate env p0 = match p0.lexpr_node with
  | PLfalse -> Pfalse
  | PLtrue -> Ptrue
  | PLrel ({lexpr_node = PLrel (_, _, t2)} as p1, op, t3) ->
      let p1 = type_predicate env p1 in
      let p2 = { lexpr_node = PLrel (t2, op, t3); lexpr_loc = p0.lexpr_loc } in
      let p2 = type_predicate env p2 in
      Pand (p1, p2)
  | PLrel (t1, (Lt | Le | Gt | Ge as r), t2) -> 
      let loc = Loc.join t1.lexpr_loc t2.lexpr_loc in
      let t1 = type_num_pointer_term env t1 in
      let t2 = type_num_pointer_term env t2 in
      if not (compatible t1 t2) then 
	error loc "comparison of incompatible types";
      Prel (t1, r, t2)
  | PLrel (t1, (Eq | Neq as r), t2) -> 
      let loc = Loc.join t1.lexpr_loc t2.lexpr_loc in
      let t1 = type_term env t1 in
      let t2 = type_term env t2 in
      if not (compatible t1 t2) then 
	error loc "comparison of incompatible types";
      Prel (t1, r, t2)
  | PLand (p1, p2) -> 
      Pand (type_predicate env p1, type_predicate env p2)
  | PLor (p1, p2) -> 
      Por (type_predicate env p1, type_predicate env p2)
  | PLimplies (p1, p2) -> 
      Pimplies (type_predicate env p1, type_predicate env p2) 
  | PLiff (p1, p2) -> 
      Piff (type_predicate env p1, type_predicate env p2) 
  | PLnot p -> 
      (match type_predicate env p with
	 | Prel (t, Neq, z) when z == zero -> Prel (t, Eq, zero)
	 | p -> Pnot p)
  | PLapp (p, tl) ->
      (try
	 let pl,info = find_pred p.logic_name in
	 let tl = type_terms p0.lexpr_loc env pl tl in
	 Papp (info, tl)
       with Not_found -> 
	 error p0.lexpr_loc ("unbound predicate " ^ p.logic_name))
  | PLif (t, p1, p2) -> 
      let t = type_int_term env t in
      Pif (t, type_predicate env p1, type_predicate env p2)
  | PLforall (q, p) -> 
      let q, env' = add_quantifiers q env in
      Pforall (q, type_predicate env' p)
  | PLexists (q, p) -> 
      let q, env' = add_quantifiers q env in
      Pexists (q, type_predicate env' p)
  | PLfresh (t) ->
      let tloc = t.lexpr_loc in
      let t = type_term env t in
      (match t.term_type.ctype_node with
	 | Tarray _ | Tpointer _ -> Pfresh(t)
	 | _ -> error tloc "subscripted value is neither array nor pointer")
  | PLvalid (t) ->
      let tloc = t.lexpr_loc in
      let t = type_term env t in
      (match t.term_type.ctype_node with
	 | Tstruct _ | Tunion _
	 | Tarray _ | Tpointer _ -> Pvalid(t)
	 | _ -> error tloc "subscripted value is neither array nor pointer")
  | PLvalid_index (t,a) ->
      let tloc = t.lexpr_loc in
      let t = type_term env t in
      let a = type_int_term env a in
      (match t.term_type.ctype_node with
	 | Tarray _ | Tpointer _ -> Pvalid_index(t,a)
	 | _ -> error tloc "subscripted value is neither array nor pointer")
  | PLvalid_range (t,a,b) ->
      let tloc = t.lexpr_loc in
      let t = type_term env t in
      let a = type_int_term env a in
      let b = type_int_term env b in
      (match t.term_type.ctype_node with
	 | Tarray _ | Tpointer _ -> Pvalid_range(t,a,b)
	 | _ -> error tloc "subscripted value is neither array nor pointer")
  | PLold p ->
      Pold (type_predicate env p)
  | PLat (p, l) ->
      (* TODO check label l *)
      Pat (type_predicate env p, l)
  | PLcast _ | PLblock_length _ | PLbase_addr _ | PLarrget _ | PLarrow _ 
  | PLdot _ | PLbinop _ | PLunop _ | PLconstant _ | PLvar _ | PLnull 
  | PLresult ->
      (*raise (Stdpp.Exc_located (p0.lexpr_loc, Parsing.Parse_error))*)
      (* interpret term [t] as [t != 0] *)
      let t = type_int_term env p0 in
      Prel (t, Neq, zero)
  | PLnamed (n, p) ->
      Pnamed (n, type_predicate env p)

let type_variant env = function 
  | (t, None) -> (type_int_term env t, None)
  | (t, r) -> (type_term env t, r)

let rec type_location env = function
  | Lterm t -> 
      Lterm (type_term env t)
  | Lstar l -> 
      Lstar (type_term env l)
  | Lrange (l1, l2, l3) -> 
      Lrange (type_term env l1, type_term env l2, type_term env l3)

let type_loop_annot env la =
  { invariant = option_app (type_predicate env) la.invariant;
    loop_assigns = option_app (List.map (type_location env)) la.loop_assigns;
    variant = option_app (type_variant env) la.variant }

let type_spec result env s = 
  let p = option_app (type_predicate env) s.requires in
  let env' = match result with
    | None -> env
    | Some ty -> Env.add "\\result" ty (Var_info (Info.default_var_info "\\result")) env
  in
  let q = option_app (type_predicate env') s.ensures in
  let v = option_app (type_variant env) s.decreases in
  let m = option_app (List.map (type_location env)) s.assigns in
  { requires = p;
    assigns = m;
    ensures = q;
    decreases = v }

