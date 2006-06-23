(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filli�tre - Claude March�
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

(*i $Id: info.ml,v 1.34 2006-06-23 15:06:02 filliatr Exp $ i*)

open Ctypes
open Creport

type why_type = 
  | Memory of why_type * zone
  | Pointer of zone
  | Addr of zone
  | Int
  | Unit
  | Why_Logic of string

and zone = 
    {
      zone_is_var : bool;
      number : int;
      mutable repr : zone option;
      name : string;
(*      mutable type_why_zone : why_type;*)
    }


let rec repr_aux z =
  match z.repr with
    | None -> z
    | Some z -> repr_aux z

(* path compression *)
let repr z =
  match z.repr with
    | None -> z
    | Some z' -> 
	let z'' = repr_aux z' in
	z.repr <- Some z''; z''

let same_zone z1 z2 =
   (repr z1) = (repr z2)
  
let rec same_why_type wt1 wt2 =
  match wt1, wt2 with
    | Pointer z1 , Pointer z2 ->
	same_zone z1 z2 
    | Memory(a1,z1), Memory(a2,z2) ->
	same_zone z1 z2 && same_why_type a1 a2
    | Int, Int -> true
    | Unit, Unit -> true
    | Why_Logic s1, Why_Logic s2 -> s1=s2
    | _, _ -> false

let rec same_why_type_no_zone wt1 wt2 =
  match wt1, wt2 with
    | Pointer z1 , Pointer z2 -> true
    | Memory(a1,z1),Memory(a2,z2) ->
	same_why_type_no_zone a1 a2
    | Int,Int -> true
    | Unit,Unit -> true
    | Why_Logic s1,Why_Logic s2 -> s1=s2
    | _, _ -> false


let found_repr ?(quote_var=true) z = 
  let z = repr z in
  if quote_var && z.zone_is_var then "'"^z.name else z.name

let rec output_why_type ty =
    match ty with
    | Int -> [], "int"
    | Pointer z -> [] , found_repr z ^ " pointer"    
    | Addr z -> [] , found_repr z ^ " addr"
    | Memory(t,z) -> (snd (output_why_type t))::[found_repr z], " memory"
    | Unit -> [], "unit"
    | Why_Logic v -> [], v


type var_info =
    {
      var_name : string;
      var_uniq_tag : int;
      mutable var_unique_name : string;
      mutable var_is_assigned : bool;
      mutable var_is_referenced : bool;
      mutable var_is_static : bool;
      mutable var_is_a_formal_param : bool;
      mutable enum_constant_value : int64;
      mutable var_type : Ctypes.ctype;
      mutable var_why_type : why_type;
    }

let tag_counter = ref 0

let default_var_info x =
  incr tag_counter;
  { var_name = x; 
    var_uniq_tag = !tag_counter;
    var_unique_name = x;
    var_is_assigned = false;
    var_is_referenced = false;
    var_is_static = false;
    var_is_a_formal_param = false;
    enum_constant_value = Int64.zero;
    var_type = c_void;
    var_why_type = Int;
  }

let set_assigned v = v.var_is_assigned <- true

let unset_assigned v = v.var_is_assigned <- false

let set_is_referenced v = v.var_is_referenced <- true

let without_dereference v f x =
  let old = v.var_is_referenced in
  try
    v.var_is_referenced <- false;
    let y = f x in
    v.var_is_referenced <- old;
    y
  with e ->
    v.var_is_referenced <- old;
    raise e

let set_static v = v.var_is_static <- true

let set_formal_param v = v.var_is_a_formal_param <- true

let unset_formal_param v = v.var_is_a_formal_param <- false

let set_const_value v n = v.enum_constant_value <- n

module HeapVarSet = 
  Set.Make(struct type t = var_info 
		  let compare i1 i2 = 
		    Pervasives.compare
		      i1.var_uniq_tag i2.var_uniq_tag 
	   end)

let print_hvs fmt s =
  HeapVarSet.iter (fun v -> Format.fprintf fmt "%s," v.var_unique_name) s

module ZoneSet = 
  Set.Make(struct type t = zone * string * why_type
		  let compare (i1,s1,_) (i2,s2,_) = 
		    match Pervasives.compare (repr i1).number 
		      (repr i2).number with
		      | 0 -> Pervasives.compare s1 s2
		      | x -> x
	   end)

type logic_info =
    {
      logic_name : string;
      mutable logic_heap_zone : ZoneSet.t;
      mutable logic_heap_args : HeapVarSet.t;
      mutable logic_args : var_info list;
      mutable logic_why_type : why_type;
      mutable logic_args_zones : zone list;
    }

let default_logic_info x =
  { logic_name = x;
    logic_heap_zone = ZoneSet.empty;
    logic_heap_args = HeapVarSet.empty;
    logic_args = [];
    logic_why_type = Unit;
    logic_args_zones = [];
  }

type fun_info =
    {
      fun_tag : int;
      fun_name : string;
      mutable fun_unique_name : string;
      mutable function_reads : ZoneSet.t;
      mutable function_writes : ZoneSet.t;
      mutable function_reads_var : HeapVarSet.t;
      mutable function_writes_var : HeapVarSet.t;
      mutable has_assigns : bool;
      mutable fun_type : Ctypes.ctype;
      mutable args : var_info list;
      mutable args_zones : zone list;
      mutable graph : fun_info list;
      mutable type_why_fun : why_type;
      mutable has_body : bool;
    }

let fun_tag_counter = ref 0

let default_fun_info x =
  { fun_tag = (let n = !fun_tag_counter in incr fun_tag_counter; n);
    fun_name = x; 
    fun_unique_name = x;
    function_reads = ZoneSet.empty;
    function_writes = ZoneSet.empty;
    function_reads_var = HeapVarSet.empty;
    function_writes_var = HeapVarSet.empty; 
    has_assigns = false;
    fun_type = c_void;
    args = [];
    args_zones = [];
    graph = [];
    type_why_fun = Int;
    has_body = false;
  }


type env_info =
  | Var_info of var_info
  | Fun_info of fun_info

let env_name e =
 match e with
    | Var_info v -> v.var_name
    | Fun_info f -> f.fun_name

let set_unique_name e n =
  match e with
    | Var_info v -> 
(*
	Coptions.lprintf "Setting unique name of %s to %s@." v.var_name n;
*)
	v.var_unique_name <- n
    | Fun_info f -> f.fun_unique_name <- n

let var_type d = 
  match d with
    | Var_info v -> v.var_type
    | Fun_info f -> f.fun_type

let set_var_type d ty whyty = match d with
  | Var_info v -> 
      Coptions.lprintf "set_var_type %s <-  %a@." v.var_name Ctypes.ctype ty;
      v.var_type <- ty;
      v.var_why_type <- whyty
  | Fun_info f -> 
      Coptions.lprintf "set_var_type %s <- %a@." f.fun_name Ctypes.ctype ty;
      f.fun_type <- ty;
      f.type_why_fun <- whyty

let set_var_type_why d whyty = match d with
  | Var_info v ->   
      v.var_why_type <- whyty
  | Fun_info f -> 
      f.type_why_fun <- whyty

