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

(*i $Id: cltyping.ml,v 1.7 2004-02-10 08:36:51 filliatr Exp $ i*)

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

let expected_type loc t1 t2 =
  if not (eq_type t1 t2) then raise_located loc (ExpectedType (t1, t2))

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
      (try
	 let (ty,_) = Env.find x env in Tvar x, ty
       with Not_found ->
	 error loc ("unbound variable " ^ x))
  | Tapp (f, tl) ->
      (try 
	 let pl, ty = find_fun f in
	 let tl = type_terms loc env pl tl in
	 Tapp (f, tl), ty
       with Not_found -> 
	 error loc ("unbound function " ^ f))
  | Tunop (op, t) -> 
      assert false
  | Tbinop (t1, op, t2) ->
      assert false
  | Tdot (t, x) ->
      assert false
  | Tarrow (t, x) ->
      assert false
  | Tarrget (t1, t2) ->
      assert false
  | Tif (t1, t2, t3) ->
      assert false
  | Told t ->
      assert false
  | Tat (t, l) ->
      assert false
  | Tlength t ->
      assert false
  | Tresult ->
      assert false

and type_terms loc env at tl =
  let rec type_list = function
    | [], [] -> 
	[]
    | et :: etl, ({info=tloc} as t) :: tl ->
	let t = type_term env t in
	expected_type tloc et t.info;
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
  | Prel (t1, r, t2) -> 
      let t1 = type_term env t1 in
      let t2 = type_term env t2 in
      (*TODO verif *) 
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
  | Pforall (x, pt, p) -> 
      let pt = type_logic_type env pt in
      let env' = Env.add x pt (Info.default_var_info x) env in
      Pforall (x, pt, type_predicate env' p)
  | Pexists (x, pt, p) -> 
      let pt = type_logic_type env pt in
      let env' = Env.add x pt (Info.default_var_info x) env in
      Pexists (x, pt, type_predicate env' p)

let type_variant env (t, r) = 
  let t = type_term env t in
  (t, r) (* TODO et=int ? *)

let type_loop_annot env (i,v) =
  option_app (type_predicate env) i, type_variant env v

let type_spec env (p,e,q) = 
  option_app (type_predicate env) p, e, option_app (type_predicate env) q

