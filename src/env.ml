(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: env.ml,v 1.2 2001-08-17 00:52:37 filliatr Exp $ *)

open Misc
open Ast
open Types
open Ident
open Logic

(* Environments for imperative programs.
 *
 * An environment of programs is an association tables
 * from identifiers (Ident.t) to types of values with effects
 * (ProgAst.ml_type_v), together with a list of these associations, since
 * the order is relevant (we have dependent types e.g. [x:nat; t:(array x T)])
 *)

module Penv = struct
  type 'a t = ('a Idmap.t)
	    * ((Ident.t * 'a) list)
	    * ((Ident.t * (Ident.t * variant)) list)
  let empty = Idmap.empty, [], []
  let add id v (m,l,r) = (Idmap.add id v m, (id,v)::l, r)
  let find id (m,_,_) = Idmap.find id m
  let fold f (_,l,_) x0 = List.fold_right f l x0
  let add_rec (id,var) (m,l,r) = (m,l,(id,var)::r)
  let find_rec id (_,_,r) = List.assoc id r
end

(* Local environments *)

type type_info = Set | TypeV of type_v

type local_env = type_info Penv.t

let empty = (Penv.empty : local_env)

let add (id,v) = Penv.add id (TypeV v)

let add_set id = Penv.add id Set

let find id env =
  match Penv.find id env with TypeV v -> v | Set -> raise Not_found

let is_local env id =
  try
    match Penv.find id env with TypeV _ -> true | Set -> false
  with
      Not_found -> false

let is_local_set env id =
  try
    match Penv.find id env with TypeV _ -> false | Set -> true
  with
      Not_found -> false


(* typed programs *)

type typing_info = {
  env : local_env;
  kappa : type_c
}
  
type typed_program = typing_info Ast.t


(* The global environment.
 *
 * We have a global typing environment env
 * We also keep a table of programs for extraction purposes
 * and a table of initializations (still for extraction)
 *)

let (env : type_info Penv.t ref) = ref Penv.empty

let (pgm_table : (typed_program option) Idmap.t ref) = ref Idmap.empty

let (init_table : term Idmap.t ref) = ref Idmap.empty

(* Operations on the global environment. *)

let is_mutable = function Ref _ | Array _ -> true | _ -> false

let add_global id v p =
  try
    let _ = Penv.find id !env in
    Error.clash id None
  with Not_found -> begin
    env := Penv.add id (TypeV v) !env; 
    pgm_table := Idmap.add id p !pgm_table
  end

let add_global_set id =
  try
    let _ = Penv.find id !env in
    Error.clash id None
  with Not_found -> 
    env := Penv.add id Set !env

let is_global id =
  try
    match Penv.find id !env with TypeV _ -> true | Set -> false
  with Not_found -> 
    false

let is_global_set id =
  try
    match Penv.find id !env with TypeV _ -> false | Set -> true
  with Not_found -> 
    false


let lookup_global id =
  match Penv.find id !env with TypeV v -> v | Set -> raise Not_found

let find_pgm id = Idmap.find id !pgm_table

let all_vars () =
  Penv.fold
    (fun (id,v) l -> match v with TypeV (Arrow _|PureType _) -> id::l | _ -> l)
    !env []

let all_refs () =
  Penv.fold
    (fun (id,v) l -> match v with TypeV (Ref _ | Array _) -> id::l | _ -> l)
    !env []

(* initializations *)

let initialize id c = init_table := Idmap.add id c !init_table

let find_init id = Idmap.find id !init_table


(* access in env, local then global *)

let type_in_env env id =
  try find id env with Not_found -> lookup_global id

let is_in_env env id =
  (is_global id) or (is_local env id)

let fold_all f lenv x0 =
  let x1 = Penv.fold f !env x0 in
  Penv.fold f lenv x1


(* recursions *)

let add_recursion = Penv.add_rec

let find_recursion = Penv.find_rec


(* We also maintain a table of the currently edited proofs of programs
 * in order to add them in the environnement when the user does Save *)

(*i
open Format

let (edited : (type_v * typed_program) Idmap.t ref) = ref Idmap.empty

let new_edited id v =
  edited := Idmap.add id v !edited

let is_edited id =
  try let _ = Idmap.find id !edited in true with Not_found -> false

let register id id' =
  try
    let (v,p) = Idmap.find id !edited in
    let _ = add_global id' v (Some p) in
    Options.if_verbose 
      mSGNL (hOV 0 [< 'sTR"Program "; pr_id id'; 'sPC; 'sTR"is defined" >]);
    edited := Idmap.remove id !edited
  with Not_found -> ()
i*)

