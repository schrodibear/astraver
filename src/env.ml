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

(*i $Id: env.ml,v 1.51 2005-11-08 15:44:45 filliatr Exp $ i*)

open Ident
open Misc
open Types
open Ast
open Logic
open Error
open Report

(* generalization *)

type 'a scheme = { scheme_vars : string list; scheme_type : 'a }

let empty_scheme t = { scheme_vars = [] ; scheme_type = t }

let rec find_pure_type_vars env t =
  match t with
    | PTvarid id ->
	let s = Ident.string id in
	if List.mem s env then env else s::env
    | PTexternal(l,id) ->
	List.fold_left find_pure_type_vars env l
    | PTint | PTreal | PTbool | PTunit | PTvar _ -> env

let find_logic_type_vars t =
  match t with
    | Function(tl,tr) ->
	let env = find_pure_type_vars [] tr in
	List.fold_left find_pure_type_vars env tl
    | Predicate(tl) ->
	List.fold_left find_pure_type_vars [] tl

let rec find_type_v_vars acc t =
  match t with
    | Ref t | PureType t -> find_pure_type_vars acc t
    | Arrow(bl,c) ->
	let acc = find_type_c_vars acc c in
	List.fold_left find_binder_vars acc bl
and find_type_c_vars acc c = find_type_v_vars acc c.c_result_type
and find_binder_vars acc (_,t) = find_type_v_vars acc t


let generalize_logic_type t =
  let l = find_logic_type_vars t in
  { scheme_vars = l ; scheme_type = t }


let rec find_predicate_vars acc p =
  match p with
    | Pvar _
    | Papp _
    | Pfpi _
    | Ptrue
    | Pfalse -> acc
    | Pimplies (_,p1,p2) 
    | Pif (_,p1,p2)
    | Pand (_,_,p1,p2)
    | Piff (p1,p2)
    | Por (p1,p2) ->
	find_predicate_vars (find_predicate_vars acc p1) p2
    | Pnot p -> find_predicate_vars acc p
    | Forall (_,_,_,t,p) 
    | Exists (_,_,t,p) ->
	find_predicate_vars (find_pure_type_vars acc t) p
    | Forallb (_,p1,p2) ->
	find_predicate_vars (find_predicate_vars acc p1) p2
    | Pnamed (_,p) ->
	find_predicate_vars acc p

let generalize_predicate p =
  let l = find_predicate_vars [] p in
  { scheme_vars = l ; scheme_type = p }

let generalize_predicate_def (bl,p) = 
  let l = 
    List.fold_left (fun acc (_,pt) -> find_pure_type_vars acc pt) [] bl 
  in
  let l = find_predicate_vars l p in
  { scheme_vars = l; scheme_type = (bl,p) }

let generalize_function_def (bl,t,e) = 
  let l = 
    List.fold_left (fun acc (_,pt) -> find_pure_type_vars acc pt) [] bl 
  in
  let l = find_pure_type_vars l t in
  { scheme_vars = l; scheme_type = (bl,t,e) }

(* specialization *)

let new_type_var =
  let c = ref 0 in
  fun () -> incr c;{ tag = !c; type_val = None }

let rec subst_pure_type s t =
  match t with
    | PTvarid id ->
	(try PTvar (List.assoc (Ident.string id) s) 
	 with Not_found -> t)
    | PTexternal(l,id) ->
	PTexternal(List.map (subst_pure_type s) l,id)
    | PTint | PTreal | PTbool | PTunit | PTvar _ -> t

let subst_logic_type s = function
  | Function (tl,tr) -> 
      Function (List.map (subst_pure_type s) tl, subst_pure_type s tr)
  | Predicate (tl) -> 
      Predicate (List.map (subst_pure_type s) tl)

let rec subst_term s = function
  | Tapp (id, tl, i) -> 
      Tapp (id, List.map (subst_term s) tl, List.map (subst_pure_type s) i)
  | Tconst _ | Tvar _ | Tderef _ as t -> 
      t

let rec subst_predicate s p =
  let f = subst_predicate s in
  match p with
  | Pimplies (w, a, b) -> Pimplies (w, f a, f b)
  | Pif (a, b, c) -> Pif (subst_term s a, f b, f c)
  | Pand (w, s, a, b) -> Pand (w, s, f a, f b)
  | Por (a, b) -> Por (f a, f b)
  | Piff (a, b) -> Piff (f a, f b)
  | Pnot a -> Pnot (f a)
  | Forall (w, id, b, v, p) -> Forall (w, id, b, subst_pure_type s v, f p)
  | Exists (id, b, v, p) -> Exists (id, b, subst_pure_type s v, f p)
  | Forallb (w, a, b) -> Forallb (w, f a, f b)
  | Papp (id, tl, i) -> 
      Papp (id, List.map (subst_term s) tl, List.map (subst_pure_type s) i)
  | Pfpi (t, a, b) -> Pfpi (subst_term s t, a, b)
  | Pnamed (n, a) -> Pnamed (n, f a)
  | Ptrue | Pfalse | Pvar _ as p -> p

let rec subst_type_v s = function
  | Ref t -> Ref (subst_pure_type s t)
  | PureType t -> PureType (subst_pure_type s t)
  | Arrow (bl,c) -> Arrow (List.map (subst_binder s) bl,subst_type_c s c)
and subst_binder s (id,t) = 
  (id, subst_type_v s t)
and subst_type_c s c =
  { c with 
    c_result_type = subst_type_v s c.c_result_type;
    c_pre = List.map (subst_predicate s) c.c_pre;
    c_post = option_app (post_app (subst_predicate s)) c.c_post }

let specialize_scheme subst s =
  let env =
    List.map
      (fun x -> (x,new_type_var()))
      s.scheme_vars
  in 
  (List.map snd env, subst env s.scheme_type)

let specialize_logic_type = specialize_scheme subst_logic_type

let specialize_type_v = specialize_scheme subst_type_v

let specialize_predicate = specialize_scheme subst_predicate

let subst_predicate_def s (bl,p) =
  let bl = List.map (fun (x,pt) -> (x, subst_pure_type s pt)) bl in
  bl, subst_predicate s p

let specialize_predicate_def = specialize_scheme subst_predicate_def

let subst_function_def s (bl,t,e) =
  let bl = List.map (fun (x,pt) -> (x, subst_pure_type s pt)) bl in
  bl, subst_pure_type s t, e

let specialize_function_def = specialize_scheme subst_function_def

(* Environments for imperative programs.
 *
 * An environment of programs is an association tables
 * from identifiers (Ident.t) to types of values with effects
 * (ProgAst.ml_type_v), together with a list of these associations, since
 * the order is relevant (we have dependent types e.g. [x:nat; t:(array x T)])
 *)

module Penv = struct
  type 'a t = 'a Idmap.t * (Ident.t * 'a) list * Idset.t
  let empty = Idmap.empty, [], Idset.empty
  let add id v (m,l,r) = (Idmap.add id v m, (id,v)::l, r)
  let find id (m,_,_) = Idmap.find id m
  let fold f (_,l,_) x0 = List.fold_right f l x0
  let iter f (_,l,_) = List.iter f l
  let add_rec x (m,l,r) = (m, l, Idset.add x r)
  let is_rec x (_,_,r) = Idset.mem x r
end


(* Local environments *)

type type_info = Set | TypeV of type_v

type local_env = type_info scheme Penv.t

let empty = (Penv.empty : local_env)

let add id v = Penv.add id (empty_scheme (TypeV v))

let add_set id = Penv.add id (empty_scheme Set)

let specialize_type_scheme s =
  match s.scheme_type with 
    | TypeV v -> specialize_type_v {s with scheme_type = v }
    | Set -> assert false (* ? *)

let find id env =
  let s = Penv.find id env in
  snd (specialize_type_scheme s)

let is_local env id =
  try
    match (Penv.find id env).scheme_type with TypeV _ -> true | Set -> false
  with Not_found -> 
    false

let is_local_set env id =
  try
    match (Penv.find id env).scheme_type with TypeV _ -> false | Set -> true
  with Not_found -> 
    false


(* typed programs *)

type typing_info = { 
  t_loc : Loc.position;
  t_env : local_env;
  t_label : label;
  t_result_name : Ident.t;
  t_result_type : type_v;
  t_effect : Effect.t;
  t_post : postcondition option 
}
  
type typed_expr = typing_info Ast.t

(* The global environment.
 *
 * We have a global typing environment env
 * We also keep a table of programs for extraction purposes
 * and a table of initializations (still for extraction)
 *)

let (env : type_info scheme Penv.t ref) = ref Penv.empty

let (pgm_table : (typed_expr option) Idmap.t ref) = ref Idmap.empty

let (init_table : term Idmap.t ref) = ref Idmap.empty

(* Operations on the global environment. *)

let generalize_type_v t =
  let l = find_type_v_vars [] t in
  { scheme_vars = l ; scheme_type = TypeV t }

let add_global_gen id v p =
  try
    let _ = Penv.find id !env in
    raise_unlocated (Clash id)
  with Not_found -> begin
    env := Penv.add id v !env; 
    pgm_table := Idmap.add id p !pgm_table
  end

let add_global id v p =
  let v = generalize_type_v v in
  add_global_gen id v p

let add_global_set id =
  try
    let _ = Penv.find id !env in
    raise_unlocated (Error.Clash id)
  with Not_found -> 
    env := Penv.add id { scheme_vars = []; scheme_type = Set} !env

let is_global id =
  try
    match (Penv.find id !env).scheme_type with TypeV _ -> true | Set -> false
  with Not_found -> 
    false

let is_global_set id =
  try
    match (Penv.find id !env).scheme_type with TypeV _ -> false | Set -> true
  with Not_found -> 
    false




let lookup_global id = find id !env

let find_pgm id = Idmap.find id !pgm_table


let all_vars () =
  let add_var (id,v) s = match v.scheme_type with
    | TypeV (Arrow _ | PureType _) -> Idset.add id s 
    | _ -> s
  in
  Penv.fold add_var !env (Idset.add t_eq (Idset.singleton t_neq))

let all_refs () =
  let add_ref (id,v) s = match v.scheme_type with
    | TypeV (Ref _) -> Idset.add id s 
    | _ -> s
  in
  Penv.fold add_ref !env Idset.empty

(* exceptions *)

let exn_table = Hashtbl.create 97

let add_exception = Hashtbl.add exn_table
let is_exception = Hashtbl.mem exn_table
let find_exception = Hashtbl.find exn_table

(* predefined exception [Exit] *)
let _ = add_exception exit_exn None

(* Logic types with their arities *) 

let types = Hashtbl.create 97

let is_type = Hashtbl.mem types

let bad_arity =
  let rec check s = function
    | [] -> false
    | v :: l -> Idset.mem v s || check (Idset.add v s) l
  in
  check Idset.empty

let add_type loc v id = 
  if is_type id then raise_located loc (ClashType id);
  if bad_arity v then raise_located loc TypeBadArity;
  Hashtbl.add types id (List.length v)

let type_arity = Hashtbl.find types

(* initializations *)

let initialize id c = init_table := Idmap.add id c !init_table

let find_init id = Idmap.find id !init_table


(* access in env, local then global *)

let type_in_env env id =
  try find id env with Not_found -> lookup_global id

let is_in_env env id =
  (is_global id) || (is_local env id)

let is_ref env id =
  try is_mutable (type_in_env env id) with Not_found -> false

let fold_all f lenv x0 =
  let f (id,s) = f (id,s.scheme_type) in
  let x1 = Penv.fold f !env x0 in
  Penv.fold f lenv x1

let add_rec = Penv.add_rec
let is_rec = Penv.is_rec


let type_v_of_logic tl tr = match tl with
  | [] -> 
      PureType tr
  | _ ->
      let binder pt = Ident.anonymous, PureType pt in
      Arrow (List.map binder tl, type_c_of_v (PureType tr))

(* Logical environment *)

type logical_env = logic_type scheme Idmap.t

let logic_table = ref Idmap.empty

let add_global_logic x t = 
  logic_table := Idmap.add x t !logic_table;
  match t.scheme_type with
    | Function (tl, tr) ->
	let v = type_v_of_logic tl tr in
	let v = { scheme_vars = t.scheme_vars ; scheme_type = TypeV v } in
	add_global_gen x v None
    | Predicate _ ->
	()

let is_global_logic x = Idmap.mem x !logic_table

let is_logic_function x =
  try 
    (match (Idmap.find x !logic_table).scheme_type with 
       | Function _ -> true 
       | _ -> false)
  with Not_found -> 
    false

let iter_global_logic f = Idmap.iter f !logic_table

let add_global_logic_gen x t =
 add_global_logic x (generalize_logic_type t)

let is_logic = Idmap.mem

let find_logic x env = specialize_logic_type (Idmap.find x env)

let add_logic_aux id vars v env = match v with
  | (Ref pt) | (PureType pt) -> 
      Idmap.add id { scheme_vars = vars ; 
		     scheme_type = (Function ([], pt)) } env
  | _ -> 
      env

let add_logic ?(generalize=true) id v env =
  let l = if generalize then find_type_v_vars [] v else [] in
  add_logic_aux id l v env

let logical_env (m,_,_) = 
  let transl m lenv = 
    Idmap.fold (fun id v e -> match v.scheme_type with 
		  | TypeV t -> add_logic_aux id v.scheme_vars t e
		  | _ -> e) m lenv
  in
  transl m (let (gm,_,_) = !env in transl gm !logic_table)
  

(*s Labels *)

module Label = struct

  module LabelSet = Set.Make(struct type t = string let compare = compare end)

  type t = LabelSet.t

  let empty = LabelSet.empty

  let add = LabelSet.add

  let mem = LabelSet.mem

end
