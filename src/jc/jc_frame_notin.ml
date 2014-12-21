(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Stdlib
open Env
open Envset
open Region
open Ast
open Fenv

open Name
open Constructors
open Common
open Separation
open Struct_tools
open Effect
open Interp_misc
open Invariants
open Pattern

open Output_ast
open Output_misc
open Format
open Why_pp

let prop_type = "prop"
(*let ft_suffix = "_ft"
let notin_suffix = "_notin"*)
let in_pred = "in_mybag"
let in_suffix = "_in"
let disj_pred = "disj_mybag"
let sub_pred = "sub_mybag"
let mybag_suffix = "mybag"
let tmp_suffix = "_tmp_name"

let jc_axiom = "_jc_axiom_"

let id_uniq = let c = ref 0 in fun () -> incr c; string_of_int !c

let remove_double compare l =
  match List.fast_sort compare l with
    | [] -> []
    | ele::l ->
        let rec aux ele = function
          | [] -> []
          | a::l when compare ele a = 0 -> aux ele l
          | a::l -> a::(aux a l) in
        ele::(aux ele l)

(** Petits Modules bien utiles *)
module MyBag =
struct
  let add_suffix s = s^"_"^mybag_suffix

  let nin = in_pred
  let ndisj = disj_pred
  let nrem = add_suffix "rem"
  let ninter = add_suffix "inter"

  let nempty = add_suffix "empty"
  let nall = add_suffix "all"

  let make_in elt set =
    LPred (nin,[elt;set])

  let empty = LVar nempty
  let all = LVar nall

  let make_rem elt set =
    if set == empty
    then empty
    else LApp(nrem,[elt;set])


  let make_inter set1 set2 =
    match set1 == all, set1, set2 == all, set2 with
      | true , _ , _ , set | _ , set, true, _ -> set
      | _ ->  LApp(ninter,[set1;set2])

  let jc_ty ty = JCTlogic (mybag_suffix,[ty])


  let ty ty =
    { lt_name = mybag_suffix;
      lt_args = [ty] }

  let ty_elt = function
    | { lt_args = [ty] } -> ty
    | _ -> assert false

  let iin =
    let pid = make_pred nin in
    let tvar = Type_var.type_var_from_string ~univ:true "a_in" in
    pid.li_poly_args <- [tvar];
    let tvar = JCTtype_var tvar in
    pid.li_parameters <- [Common.var tvar "x";
                                     Common.var (jc_ty tvar) "s"];
    pid

  let make_jc_in l =
    new assertion (JCAapp
                     {
                       app_fun = iin;
                       app_args = l;
                       app_region_assoc = [];
                       app_label_assoc = []
                     })

  let idisj =
    let pid = make_pred ndisj in
    let tvar = Type_var.type_var_from_string ~univ:true "a" in
    pid.li_poly_args <- [tvar];
    let tvar = JCTtype_var tvar in
    pid.li_parameters <- [Common.var (jc_ty tvar) "s1";
                                     Common.var (jc_ty tvar) "s2"];
    pid

  let make_jc_disj l =
    new assertion (JCAapp
                     {
                       app_fun = idisj;
                       app_args = l;
                       app_region_assoc = [];
                       app_label_assoc = []
                     })


  let isub =
    let pid = make_pred sub_pred in
    let tvar = Type_var.type_var_from_string ~univ:true "a" in
    pid.li_poly_args <- [tvar];
    let tvar = JCTtype_var tvar in
    pid.li_parameters <- [Common.var (jc_ty tvar) "s1";
                                     Common.var (jc_ty tvar) "s2"];
    pid

  let make_jc_sub l =
    new assertion (JCAapp
                     {
                       app_fun = isub;
                       app_args = l;
                       app_region_assoc = [];
                       app_label_assoc = []
                     })




  type elt_set =
      [ `Empty | `All | `MyBag of term
      | `Elt of term]

  (* this order is important *)
  let num = function
    | `Empty -> 1
    | `All -> 2
    | `Elt _ -> 3
    | `MyBag _ -> 4

  let compare e1 e2 =
    let c = compare (num e1) (num e2) in
    if c <> 0 then c else compare e1 e2

  let print fmt : elt_set -> unit =
    let module Output = (val Options.backend) in
    function
    | `Empty -> fprintf fmt "empty"
    | `All -> fprintf fmt "all"
    | `MyBag s -> fprintf fmt "mybag(%a)" Output.fprintf_term s
    | `Elt s -> fprintf fmt "elt(%a)" Output.fprintf_term s

 (* let make_inter_rem_list (l:elt_set list) =
    let rec aux  = function
    | [] -> all
    | `Empty::_ -> empty
    | `All::l -> aux l
    | `MyBag s::l -> make_inter s (aux l)
    | `Elt e::l -> make_rem e (aux l) in
    let l_s = remove_double compare l in
    Options.lprintf "make_inter_rem : %a" (print_list comma print) l_s;
    aux l_s
 *)
end



module NotIn =
struct
  type t = {
    for_one : bool; (*true if its not a bag but one element (a singleton) *)
    mem : Memory.t;
    label : label;
    mem_name : string;
    name : string;
    ty_mem : logic_type;
  }

  let compare t1 t2 = Memory.compare t1.mem t2.mem

  let from_memory for_one (((mc,_distr) as m),label) =
    let (s,_,_) = tr_li_model_mem_arg_3 ~label_in_name:true label m
      (*memory_name (mc,distr)*) in
    if for_one
    then
      {for_one = true;
       mem = m;
       label = label;
       mem_name = s;
       name = s^in_suffix^"_elt";
       ty_mem = memory_type mc}
    else
      {for_one = false;
       mem = m;
       label = label;
       mem_name = s;
       name = s^in_suffix;
       ty_mem = memory_type mc}

  let is_memory t m =
    (*Options.lprintf "is_memory : %s = %s@." m t.mem_name;*)
    m = t.mem_name
  let is_memory_var t = function
    | LVar m -> is_memory t m
    | _ -> false

  let notin_args t = LVar (t.name)

  let for_one t = t.for_one
  let name t = t.name
  let var t = LVar t.name
  let ty_elt t = raw_pointer_type (fst (deconstruct_memory_type_args t.ty_mem))
  let ty_elt_val t = snd (deconstruct_memory_type_args t.ty_mem)

  let jc_ty_elt t =
    let root = match alloc_class_of_mem_class (fst t.mem) with
      | JCalloc_root r -> r
      | JCalloc_bitvector -> assert false in
    JCTpointer(JCroot root,None,None)

  let jc_ty t = MyBag.jc_ty (jc_ty_elt t)

  let ty t =
    let ty = ty_elt t in
    if t.for_one
    then ty
    else MyBag.ty ty

  let mem_name t = t.mem_name
  let mem_name2 t =
    let mem_name = memory_name t.mem in
    if t.for_one
    then mem_name^"_elt"
    else mem_name
end

module NotInSet = Set.Make(NotIn)
module NotInMap = Map.Make(NotIn)


let in_name notin s = s^(NotIn.mem_name2 notin)^in_suffix

let get_in_logic =
  let memo = Hashtbl.create 10 in
  fun f notin ->
    try
      Hashtbl.find memo (f.li_tag,notin)
    with Not_found ->
      let fin = make_logic_fun (in_name notin f.li_name)
        (NotIn.jc_ty notin) in
      fin.li_result_region <- f.li_result_region;
      fin.li_poly_args <- f.li_poly_args;
      fin.li_parameters <- f.li_parameters;
      fin.li_param_regions <- f.li_param_regions;
      fin.li_effects <- f.li_effects;
      fin.li_labels <- f.li_labels;
      IntHashtblIter.add Typing.logic_functions_table fin.li_tag
        (fin,JCNone);
      Hashtbl.add memo (f.li_tag,notin) fin;
      fin

let app_in_logic f fparams label notin =
  let fin = get_in_logic f notin in
  let app = {app_fun = fin;
             app_args = fparams;
             app_region_assoc = [];
             app_label_assoc =
      List.map (fun e -> (e,label)) fin.li_labels} in
  new term (NotIn.jc_ty notin) (JCTapp app)
