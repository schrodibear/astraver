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

(*i $Id: cltyping.ml,v 1.15 2004-02-23 15:30:13 filliatr Exp $ i*)

open Cast
open Clogic
open Creport
open Cerror
open Cenv

let option_app f = function Some x -> Some (f x) | None -> None

(* Typing terms *)

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
let c_pointer ty = noattr (CTpointer ty)
let c_void_star = c_pointer c_void

let is_null t = t.node = Tnull

let compatible t1 t2 = 
  sub_type t1.info t2.info || 
  sub_type t2.info t1.info ||
  (pointer_or_array_type t1.info && is_null t2) ||
  (pointer_or_array_type t2.info && is_null t1)

let expected_type loc t1 t2 =
  if not (eq_type t1 t2) then raise_located loc (ExpectedType (t1, t2))

let expected_num loc t = match t.info.ctype_node with
  | CTint _ | CTfloat _ -> ()
  | _ -> error loc "invalid operand (expected integer or float)"

let expected_int loc t = match t.info.ctype_node with
  | CTint _ -> ()
  | _ -> error loc "invalid operand (expected integer)"

let max_type t1 t2 = match t1.ctype_node, t2.ctype_node with
  | CTint _, CTint _ -> c_int
  | CTint _, CTfloat _
  | CTfloat _, CTint _
  | CTfloat _, CTfloat _ -> c_float
  | _ -> assert false

(* Typing terms *)

let rec type_term env t =
  let t, ty = type_term_node t.info env t.node in
  { node = t; info = ty }

and type_term_node loc env = function
  | Tconstant c -> 
      (try 
	 let _ = int_of_string c in Tconstant c, c_int
       with _ -> 
	 Tconstant c, c_float)
  | Tvar x ->
      let (ty,_) = 
	try Env.find x env with Not_found -> 
	try find_sym x with Not_found -> 
        error loc ("unbound variable " ^ x)
      in 
      Tvar x, ty
  | Tapp (f, tl) ->
      (try 
	 let pl, ty = find_fun f in
	 let tl = type_terms loc env pl tl in
	 Tapp (f, tl), ty
       with Not_found -> 
	 error loc ("unbound function " ^ f))
  | Tunop (Uminus, t) -> 
      let t = type_num_term env t in
      Tunop (Uminus, t), t.info
  | Tunop (Ustar, t) -> 
      let t = type_term env t in
      begin match t.info.ctype_node with
	| CTpointer ty | CTarray (ty, _) -> Tunop (Ustar, t), ty
	| _ -> error loc "invalid type argument of `unary *'"
      end
   | Tbinop (t1, (Badd | Bsub | Bmul | Bdiv as op), t2) ->
      let t1 = type_num_term env t1 in
      let t2 = type_num_term env t2 in
      Tbinop (t1, op, t2), max_type t1.info t2.info
  | Tbinop (t1, Bmod, t2) ->
      let t1 = type_int_term env t1 in
      let t2 = type_int_term env t2 in
      Tbinop (t1, Bmod, t2), c_int
  | Tdot (t, x) ->
      let t = type_term env t in
      Tdot (t, x), type_of_field loc env x t.info
  | Tarrow (t, x) ->
      let t = type_term env t in
      begin match t.info.ctype_node with
	| CTpointer ty -> 
	    Tarrow (t, x), type_of_field loc env x ty
	| _ -> 
	    error loc "invalid type argument of `->'"
      end
  | Tarrget (t1, t2) ->
      let t1 = type_term env t1 in
      (match t1.info.ctype_node with
	 | CTarray (ty, _) | CTpointer ty ->
	     let t2 = type_int_term env t2 in
	     Tarrget (t1, t2), ty
	 | _ ->
	     error loc "subscripted value is neither array nor pointer")
  | Tif (t1, t2, t3) ->
      (* TODO type de t1 ? *)
      assert false (*TODO*)
  | Told t ->
      let t = type_term env t in
      Told t, t.info
  | Tat (t, l) ->
      (* TODO check label l *)
      let t = type_term env t in
      Tat (t, l), t.info
  | Tlength t ->
      let t = type_term env t in
      (match t.info.ctype_node with
	 | CTarray _ | CTpointer _ -> Tlength t, c_int
	 | _ -> error loc "subscripted value is neither array nor pointer")
  | Tresult ->
      (try let ty,_ = Env.find "\\result" env in Tresult, ty
       with Not_found -> error loc "\\result meaningless")
  | Tnull ->
      Tnull, c_void_star

and type_int_term env t =
  let tt = type_term env t in
  expected_int t.info tt;
  tt

and type_num_term env t =
  let tt = type_term env t in
  expected_num t.info tt;
  tt

and type_terms loc env at tl =
  let rec type_list = function
    | [], [] -> 
	[]
    | et :: etl, ({info=tloc} as t) :: tl ->
	let t = type_term env t in
	expected_type tloc t.info et;
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
  | CTint _ | CTfloat _ as t -> t
  | CTarray (ty, None) -> CTarray (type_type env ty, None)
  | _ -> assert false

let rec type_logic_type env = function
  | LTint -> c_int
  | LTfloat -> c_float
  | LTarray ty -> c_array (type_logic_type env ty)
  | LTpointer ty -> c_pointer (type_logic_type env ty)
  | LTvar id -> noattr (CTvar id)

(** abandon provisoire 
let rec type_logic_type env = function
  | PTctype ct ->
      PTctype (type_type env ct)
  | PTvar {tag=n; type_val =t } -> 
      PTvar { tag = n; type_val = option_app (type_logic_type env) t }
  | PTexternal (tl, s) -> 
      PTexternal (List.map (type_logic_type env) tl, s)
**)

let type_quantifier env (ty, x) = (type_logic_type env ty, x)
let type_quantifiers env = List.map (type_quantifier env)

let add_quantifiers q env =
  List.fold_left
    (fun env (ty, x) -> Env.add x ty (Info.default_var_info x) env)
    env q

(* Typing predicates *)

let rec type_predicate env = function
  | Pfalse
  | Ptrue as p -> 
      p
  | Pvar (loc, x) -> 
      (try 
	 (match find_pred x with
	    | [] -> Pvar (loc, x)
	    | _ -> error loc ("predicate " ^ x ^ " expects arguments"))
       with Not_found -> error loc ("unbound predicate " ^ x))
  | Prel (t1, (Lt | Le | Gt | Ge as r), t2) -> 
      let t1 = type_num_term env t1 in
      let t2 = type_num_term env t2 in
      Prel (t1, r, t2)
  | Prel (t1, (Eq | Neq as r), t2) -> 
      let loc = Loc.join t1.info t2.info in
      let t1 = type_term env t1 in
      let t2 = type_term env t2 in
      if not (compatible t1 t2) then 
	error loc "comparison of incompatible types";
      Prel (t1, r, t2)
  | Pand (p1, p2) -> 
      Pand (type_predicate env p1, type_predicate env p2)
  | Por (p1, p2) -> 
      Por (type_predicate env p1, type_predicate env p2)
  | Pimplies (p1, p2) -> 
      Pimplies (type_predicate env p1, type_predicate env p2) 
  | Pnot p -> 
      Pnot (type_predicate env p)
  | Papp (locp, p, tl) ->
      (try
	 let pl = find_pred p in
	 let tl = type_terms locp env pl tl in
	 Papp (locp, p, tl)
       with Not_found -> 
	 error locp ("unbound predicate " ^ p))
  | Pif (t, p1, p2) -> 
      (* TODO type t ? *)
      let t = type_term env t in
      Pif (t, type_predicate env p1, type_predicate env p2)
  | Pforall (q, p) -> 
      let q = type_quantifiers env q in
      let env' = add_quantifiers q env in
      Pforall (q, type_predicate env' p)
  | Pexists (q, p) -> 
      let q = type_quantifiers env q in
      let env' = add_quantifiers q env in
      Pexists (q, type_predicate env' p)

let type_variant env = function 
  | (t, None) -> (type_int_term env t, None)
  | (t, r) -> (type_term env t, r)

let type_loop_annot env la =
  { invariant = option_app (type_predicate env) la.invariant;
    variant = option_app (type_variant env) la.variant }

let rec type_location env = function
  | Lterm t -> 
      Lterm (type_term env t)
  | Lstar l -> 
      Lstar (type_term env l)
  | Lrange (l1, l2, l3) -> 
      Lrange (type_term env l1, type_term env l2, type_term env l3)

let type_spec ~result:ty env s = 
  let p = option_app (type_predicate env) s.requires in
  let env' = Env.add "\\result" ty (Info.default_var_info "\\result") env in
  let q = option_app (type_predicate env') s.ensures in
  let v = option_app (type_variant env) s.decreases in
  let m = List.map (type_location env) s.assigns in
  { requires = p;
    assigns = m;
    ensures = q;
    decreases = v }

