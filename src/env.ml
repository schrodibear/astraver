(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: env.ml,v 1.21 2002-07-08 13:21:27 filliatr Exp $ i*)

open Ident
open Misc
open Ast
open Types
open Logic
open Error
open Report

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

type local_env = type_info Penv.t

let empty = (Penv.empty : local_env)

let add id v = Penv.add id (TypeV v)

let add_set id = Penv.add id Set

let find id env =
  match Penv.find id env with TypeV v -> v | Set -> raise Not_found

let is_local env id =
  try
    match Penv.find id env with TypeV _ -> true | Set -> false
  with Not_found -> 
    false

let is_local_set env id =
  try
    match Penv.find id env with TypeV _ -> false | Set -> true
  with Not_found -> 
    false

(* typed programs *)

type typing_info = {
  env : local_env;
  label : string;
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

let add_global id v p =
  try
    let _ = Penv.find id !env in
    raise_unlocated (Clash id)
  with Not_found -> begin
    env := Penv.add id (TypeV v) !env; 
    pgm_table := Idmap.add id p !pgm_table
  end

let add_global_set id =
  try
    let _ = Penv.find id !env in
    raise_unlocated (Error.Clash id)
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
  let add_var (id,v) s = match v with
    | TypeV (Arrow _ | PureType _) -> Idset.add id s 
    | _ -> s
  in
  Penv.fold add_var !env (Idset.add t_eq (Idset.singleton t_neq))

let all_refs () =
  let add_ref (id,v) s = match v with
    | TypeV (Ref _ | Array _) -> Idset.add id s 
    | _ -> s
  in
  Penv.fold add_ref !env Idset.empty

(* exceptions *)

let exn_table = Hashtbl.create 97

let add_exception = Hashtbl.add exn_table
let is_exception = Hashtbl.mem exn_table
let find_exception = Hashtbl.find exn_table


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
let float = PureType PTfloat

let compare_type op t =
  let q = Pif (Tvar result,
	       relation op (Tvar x) (Tvar y),
	       not_relation op (Tvar x) (Tvar y))
  in
  make_arrow 
    [x, BindType t; y, BindType t]
    { c_result_name = result;
      c_result_type = bool;
      c_effect = Effect.bottom;
      c_pre = []; c_post = Some (anonymous q) }

let _ = add_global t_lt_int (compare_type t_lt_int int) None
let _ = add_global t_le_int (compare_type t_le_int int) None
let _ = add_global t_gt_int (compare_type t_gt_int int) None
let _ = add_global t_ge_int (compare_type t_ge_int int) None

let _ = add_global t_lt_float (compare_type t_lt_float float) None
let _ = add_global t_le_float (compare_type t_le_float float) None
let _ = add_global t_gt_float (compare_type t_gt_float float) None
let _ = add_global t_ge_float (compare_type t_ge_float float) None

let _ = add_global t_eq_int (compare_type t_eq_int int) None
let _ = add_global t_eq_unit (compare_type t_eq_unit unit) None
let _ = add_global t_eq_bool (compare_type t_eq_bool bool) None
let _ = add_global t_eq_float (compare_type t_eq_float float) None

let _ = add_global t_neq_int (compare_type t_neq_int int) None
let _ = add_global t_neq_unit (compare_type t_neq_unit unit) None
let _ = add_global t_neq_bool (compare_type t_neq_bool bool) None
let _ = add_global t_neq_float (compare_type t_neq_float float) None

let bin_arith_type t = 
  make_arrow 
    [x, BindType t; y, BindType t]
    { c_result_name = result;
      c_result_type = t;
      c_effect = Effect.bottom;
      c_pre = []; c_post = None }

let _ = add_global t_add_int (bin_arith_type int) None
let _ = add_global t_sub_int (bin_arith_type int) None
let _ = add_global t_mul_int (bin_arith_type int) None
let _ = add_global t_div_int (bin_arith_type int) None
let _ = add_global t_mod     (bin_arith_type int) None

let _ = add_global t_add_float (bin_arith_type float) None
let _ = add_global t_sub_float (bin_arith_type float) None
let _ = add_global t_mul_float (bin_arith_type float) None
let _ = add_global t_div_float (bin_arith_type float) None

let un_arith_type t = 
  make_arrow 
    [x, BindType t]
    { c_result_name = result;
      c_result_type = t;
      c_effect = Effect.bottom;
      c_pre = []; c_post = None }

let _ = add_global t_neg_int (un_arith_type int) None
let _ = add_global t_neg_float (un_arith_type float) None

(* Logical environment *)

type logical_env = logic_type Idmap.t

let logic_table = ref Idmap.empty

let add_global_logic x t = logic_table := Idmap.add x t !logic_table

let int_array = PTarray (Tvar Ident.implicit, PTint)
let agl s = add_global_logic (Ident.create s)

let _ = agl "sorted_array" (Predicate [int_array; PTint; PTint])
let _ = agl "exchange"     (Predicate [int_array; int_array; PTint; PTint])
let _ = agl "sub_permut"   (Predicate [PTint; PTint; int_array; int_array])
let _ = agl "permut"       (Predicate [int_array; int_array])
let _ = agl "array_le"     (Predicate [int_array; PTint; PTint; PTint])
let _ = agl "array_ge"     (Predicate [int_array; PTint; PTint; PTint])

let is_logic = Idmap.mem
let find_logic = Idmap.find

let add_logic id v env = match v with
  | (Ref (PureType pt)) | (PureType pt) -> 
      Idmap.add id (Function ([], pt)) env
  | (Array (n, PureType t)) -> 
      Idmap.add id (Function ([], PTarray (n,t))) env
  | _ -> 
      env

let logical_env (m,_,_) = 
  let transl m lenv = 
    Idmap.fold (fun id v e -> match v with 
		  | TypeV v -> add_logic id v e
		  | _ -> e) m lenv
  in
  transl m (let (gm,_,_) = !env in transl gm !logic_table)
  

(*s Labels *)

module LabelSet = Set.Make(struct type t = string let compare = compare end)

let initial_labels = LabelSet.singleton "init"

