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

(*i $Id: env.ml,v 1.43 2004-05-25 12:33:03 filliatr Exp $ i*)

open Ident
open Misc
open Ast
open Types
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
    | PTarray ta -> find_pure_type_vars env ta
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
    | Ref t | Array t -> find_type_v_vars acc t
    | Arrow(bl,c) ->
	let acc = find_type_c_vars acc c in
	List.fold_left find_binder_vars acc bl
    | PureType t -> find_pure_type_vars acc t
and find_type_c_vars acc c = find_type_v_vars acc c.c_result_type
and find_binder_vars acc (_,b) =
  match b with
    | BindType t -> find_type_v_vars acc t
    | BindSet | Untyped -> acc


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
    | Pand (_,p1,p2)
    | Piff (p1,p2)
    | Por (p1,p2) ->
	find_predicate_vars (find_predicate_vars acc p1) p2
    | Pnot p -> find_predicate_vars acc p
    | Forall (_,_,_,t,p) 
    | Exists (_,_,t,p) ->
	find_predicate_vars (find_pure_type_vars acc t) p
    | Forallb (_,_,_,p1,p2,p3) ->
	find_predicate_vars 
	  (find_predicate_vars (find_predicate_vars acc p1) p2) p3

let generalize_predicate p =
  let l = find_predicate_vars [] p in
  { scheme_vars = l ; scheme_type = p }

let generalize_predicate_def (bl,p) = 
  let l = 
    List.fold_left (fun acc (_,pt) -> find_pure_type_vars acc pt) [] bl 
  in
  let l = find_predicate_vars l p in
  { scheme_vars = l; scheme_type = (bl,p) }

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
    | PTarray ta -> PTarray (subst_pure_type s ta)
    | PTint | PTreal | PTbool | PTunit | PTvar _ -> t

let subst_logic_type s t =
  match t with
    | Function(tl,tr) -> 
	Function(List.map (subst_pure_type s) tl,subst_pure_type s tr)
    | Predicate(tl) -> 
	Predicate(List.map (subst_pure_type s) tl)

let rec subst_type_v s t =
  match t with
  | Ref t -> Ref (subst_type_v s t)
  | Array t -> Array (subst_type_v s t)
  | Arrow(bl,c) ->
      Arrow(List.map (subst_binder s) bl,subst_type_c s c)
  | PureType t -> PureType(subst_pure_type s t)
and subst_binder s ((id,t) as b) =
  match t with
    | BindSet | Untyped -> b
    | BindType t -> (id,BindType (subst_type_v s t))
and subst_type_c s c =
  { c with c_result_type = subst_type_v s c.c_result_type }

let specialize_scheme subst s =
  let env =
    List.map
      (fun x -> (x,new_type_var()))
      s.scheme_vars
  in 
  (List.map snd env,subst env s.scheme_type)

let specialize_logic_type = specialize_scheme subst_logic_type

let specialize_type_v = specialize_scheme subst_type_v

let rec subst_predicate s p =
  let f = subst_predicate s in
  match p with
  | Pimplies (w, a, b) -> Pimplies (w, f a, f b)
  | Pif (a, b, c) -> Pif (a, f b, f c)
  | Pand (w, a, b) -> Pand (w, f a, f b)
  | Por (a, b) -> Por (f a, f b)
  | Piff (a, b) -> Piff (f a, f b)
  | Pnot a -> Pnot (f a)
  | Forall (w, id, b, v, p) -> Forall (w, id, b, subst_pure_type s v, f p)
  | Exists (id, b, v, p) -> Exists (id, b, subst_pure_type s v, f p)
  | Forallb (w, id, v, p, a, b) -> Forallb (w, id, v, f p, f a, f b)
  | Ptrue | Pfalse | Pvar _ | Papp _ | Pfpi _ as p -> p

let specialize_predicate = specialize_scheme subst_predicate

let subst_predicate_def s (bl,p) =
  let bl = List.map (fun (x,pt) -> (x, subst_pure_type s pt)) bl in
  bl, subst_predicate s p

let specialize_predicate_def = specialize_scheme subst_predicate_def

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
  loc : Loc.t;
  env : local_env;
  label : string;
  obligations : assertion list;
  kappa : type_c
}
  
type typed_program = typing_info Ast.t

(* The global environment.
 *
 * We have a global typing environment env
 * We also keep a table of programs for extraction purposes
 * and a table of initializations (still for extraction)
 *)

let (env : type_info scheme Penv.t ref) = ref Penv.empty

let (pgm_table : (typed_program option) Idmap.t ref) = ref Idmap.empty

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
    | TypeV (Ref _ | Array _) -> Idset.add id s 
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


(* Initial symbol table *)

let x = Ident.create "x"
let y = Ident.create "y"
let int = PureType PTint
let bool = PureType PTbool
let unit = PureType PTunit
let real = PureType PTreal

let make_c t q = 
  { c_result_name = result; c_result_type = t;
    c_effect = Effect.bottom; c_pre = []; c_post = q }

let compare_type op t =
  let q = Pif (Tvar result,
	       relation op (Tvar x) (Tvar y),
	       not_relation op (Tvar x) (Tvar y))
  in
  let q = make_c bool (Some (anonymous Loc.dummy q, [])) in
  make_arrow [x, BindType t; y, BindType t] q

let _ = add_global t_lt_int (compare_type t_lt_int int) None
let _ = add_global t_le_int (compare_type t_le_int int) None
let _ = add_global t_gt_int (compare_type t_gt_int int) None
let _ = add_global t_ge_int (compare_type t_ge_int int) None

let _ = add_global t_lt_real (compare_type t_lt_real real) None
let _ = add_global t_le_real (compare_type t_le_real real) None
let _ = add_global t_gt_real (compare_type t_gt_real real) None
let _ = add_global t_ge_real (compare_type t_ge_real real) None

let _ = add_global t_eq_int (compare_type t_eq_int int) None
let _ = add_global t_eq_unit (compare_type t_eq_unit unit) None
let _ = add_global t_eq_bool (compare_type t_eq_bool bool) None
let _ = add_global t_eq_real (compare_type t_eq_real real) None

let _ = add_global t_neq_int (compare_type t_neq_int int) None
let _ = add_global t_neq_unit (compare_type t_neq_unit unit) None
let _ = add_global t_neq_bool (compare_type t_neq_bool bool) None
let _ = add_global t_neq_real (compare_type t_neq_real real) None

let bin_arith_type t = 
  make_arrow [x, BindType t; y, BindType t] (make_c t None)

let _ = add_global t_add_int (bin_arith_type int) None
let _ = add_global t_sub_int (bin_arith_type int) None
let _ = add_global t_mul_int (bin_arith_type int) None
let _ = add_global t_div_int (bin_arith_type int) None
let _ = add_global t_mod_int (bin_arith_type int) None

let _ = add_global t_add_real (bin_arith_type real) None
let _ = add_global t_sub_real (bin_arith_type real) None
let _ = add_global t_mul_real (bin_arith_type real) None
let _ = add_global t_div_real (bin_arith_type real) None

let un_arith_type t = 
  make_arrow [x, BindType t] (make_c t None)

let _ = add_global t_neg_int (un_arith_type int) None
let _ = add_global t_neg_real (un_arith_type real) None
let _ = add_global t_sqrt_real (un_arith_type real) None

let _ = add_global t_real_of_int 
	  (make_arrow [x, BindType int] (make_c real None)) None
let _ = add_global t_int_of_real
	  (make_arrow [x, BindType real] (make_c int None)) None

let any t = 
  make_arrow [x, BindType unit] 
    (make_c t (Some (anonymous Loc.dummy Ptrue, [])))
let _ = add_global any_int (any int) None
let _ = add_global any_unit (any unit) None
let _ = add_global any_real (any real) None

(* Logical environment *)

type logical_env = logic_type scheme Idmap.t

let logic_table = ref Idmap.empty

let add_global_logic x t = 
  logic_table := Idmap.add x t !logic_table

let iter_global_logic f = Idmap.iter f !logic_table

let add_global_logic_gen x t =
 add_global_logic x (generalize_logic_type t)

let int_array = PTarray PTint
let agl s = add_global_logic_gen (Ident.create s)

let int_cmp = Predicate [PTint; PTint]
let _ = agl "lt_int" int_cmp
let _ = agl "le_int" int_cmp
let _ = agl "gt_int" int_cmp
let _ = agl "ge_int" int_cmp
let _ = agl "eq_int" int_cmp
let _ = agl "neq_int" int_cmp

let real_cmp = Predicate [PTreal; PTreal]
let _ = agl "lt_real" real_cmp
let _ = agl "le_real" real_cmp
let _ = agl "gt_real" real_cmp
let _ = agl "ge_real" real_cmp
let _ = agl "eq_real" real_cmp
let _ = agl "neq_real" real_cmp

let _ = agl "eq_bool" (Predicate [PTbool; PTbool])
let _ = agl "neq_bool" (Predicate [PTbool; PTbool])
let _ = agl "eq_unit" (Predicate [PTunit; PTunit])
let _ = agl "neq_unit" (Predicate [PTunit; PTunit])

let int_binop_arith = Function ([PTint; PTint], PTint)
let _ = agl "add_int" int_binop_arith
let _ = agl "sub_int" int_binop_arith
let _ = agl "mul_int" int_binop_arith
let _ = agl "div_int" int_binop_arith
let _ = agl "mod_int" int_binop_arith
let _ = agl "neg_int" (Function ([PTint], PTint))

let real_binop_arith = Function ([PTreal; PTreal], PTreal)
let _ = agl "add_real" real_binop_arith
let _ = agl "sub_real" real_binop_arith
let _ = agl "mul_real" real_binop_arith
let _ = agl "div_real" real_binop_arith
let _ = agl "neg_real" (Function ([PTreal], PTreal))
let _ = agl "sqrt_real" (Function ([PTreal], PTreal))
let _ = agl "real_of_int" (Function ([PTint], PTreal))
let _ = agl "int_of_real" (Function ([PTreal], PTint))

let _ = agl "sorted_array" (Predicate [int_array; PTint; PTint])
let _ = agl "exchange"     (Predicate [int_array; int_array; PTint; PTint])
let _ = agl "sub_permut"   (Predicate [PTint; PTint; int_array; int_array])
let _ = agl "permut"       (Predicate [int_array; int_array])
let _ = agl "array_le"     (Predicate [int_array; PTint; PTint; PTint])
let _ = agl "array_ge"     (Predicate [int_array; PTint; PTint; PTint])

let is_logic = Idmap.mem

let find_logic x env = snd (specialize_logic_type (Idmap.find x env))

let add_logic_aux id vars v env = match v with
  | (Ref (PureType pt)) | (PureType pt) -> 
      Idmap.add id { scheme_vars = vars ; 
		     scheme_type = (Function ([], pt)) } env
  | (Array (PureType t)) -> 
      Idmap.add id { scheme_vars = vars ; 
		     scheme_type = (Function ([], PTarray t)) } env
  | _ -> 
      env

let add_logic id v env =
  let l = find_type_v_vars [] v in
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
