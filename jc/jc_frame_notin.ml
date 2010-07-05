(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2010                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS                                     *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*    Thierry HUBERT, Univ. Paris-sud 11                                  *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
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

open Jc_stdlib
open Jc_env
open Jc_envset
open Jc_region
open Jc_ast
open Jc_fenv

open Jc_name
open Jc_constructors
open Jc_pervasives
open Jc_separation
open Jc_struct_tools
open Jc_effect
open Jc_interp_misc
open Jc_invariants
open Jc_pattern

open Output
open Format
open Pp

let prop_type = "prop"
(*let ft_suffix = "_ft"
let notin_suffix = "_notin"*)
let in_pred = "in_mybag"
let in_suffix = "_in"
let disj_pred = "disj_mybag"
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

  let nin = add_suffix "in"
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

  let ty ty = { logic_type_name = mybag_suffix;
                        logic_type_args = [ty]
              }

  let ty_elt = function
    | {logic_type_args = [ty]} -> ty
    | _ -> assert false


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

  let print fmt : elt_set -> unit = function
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
    Jc_options.lprintf "make_inter_rem : %a" (print_list comma print) l_s;
    aux l_s
 *)
end
