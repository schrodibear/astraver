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

(*i $Id: cltyping.ml,v 1.2 2004-02-04 13:45:19 filliatr Exp $ i*)

open Cast
open Clogic
open Creport
open Cerror

(*s Environments for the logical side *)

module Smap = Map.Make(String)

type env = { 
  functions : (tctype list * tctype) Smap.t; 
  predicates : tctype list Smap.t 
}

let empty = { functions = Smap.empty; predicates = Smap.empty }

let add_fun f pl env = { env with functions = Smap.add f pl env.functions }
let find_fun f env = Smap.find f env.functions

let add_pred p pl env = { env with predicates = Smap.add p pl env.predicates }
let find_pred p env = Smap.find p env.predicates

let option_app f = function Some x -> Some (f x) | None -> None

let error l s = raise (Error (Some l, AnyMessage s))

(* Typing terms *)

let rec type_term env et t =
  assert false (*TODO*)

and type_terms loc env at tl =
  let rec type_list = function
    | [], [] -> 
	[]
    | et :: etl, t :: tl ->
	let t = type_term env (Some et) t in
	t :: type_list (etl, tl)
    | [], _ ->
	raise_located loc TooManyArguments
    | _, [] ->
	raise_located loc PartialApp
  in
  type_list (at, tl)

(* Typing predicates *)

let rec type_predicate env = function
  | Pfalse
  | Ptrue as p -> 
      p
  | Pvar { node = x; info = loc } -> 
      (try 
	 (match find_pred x env with
	    | [] -> Pvar x
	    | _ -> error loc ("predicate " ^ x ^ " expects arguments"))
       with Not_found -> error loc ("unbound predicate " ^ x))
  | Prel (t1, r, t2) -> 
      (*TODO*) Prel (type_term env None t1, r, type_term env None t2)
  | Pand (p1, p2) -> 
      Pand (type_predicate env p1, type_predicate env p2)
  | Por (p1, p2) -> 
      Por (type_predicate env p1, type_predicate env p2)
  | Pimplies (p1, p2) -> 
      Pimplies (type_predicate env p1, type_predicate env p2) 
  | Pnot p -> 
      Pnot (type_predicate env p)
  | Papp ({node=p; info=locp}, tl) ->
      (try
	 let pl = find_pred p env in
	 let tl = type_terms locp env pl tl in
	 Papp (p, tl)
       with Not_found -> 
	 error locp ("unbound predicate " ^ p))
  | Pif (t, p1, p2) -> 
      Pif (type_term env None t, type_predicate env p1,
	   type_predicate env p2)
  | Pforall (s, pt, p) -> 
      Pforall (s, pt, type_predicate env p)
  | Pexists (s, pt, p) -> 
      Pexists (s, pt, type_predicate env p)

let type_variant env (t, r) = (type_term env None t, r) (* TODO et=int ? *)

let type_loop_annot env (i,v) =
  option_app (type_predicate env) i, type_variant env v

let type_spec env (p,e,q) = 
  option_app (type_predicate env) p, e, option_app (type_predicate env) q

