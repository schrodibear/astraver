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

(*i $Id: effect.ml,v 1.17 2002-10-17 15:01:53 filliatr Exp $ i*)

(*s Effects. *)

open Ident

(*s An effect is composed of three sets of variables.

    The first one is the set of all variables (the input),
    the second one is the set of possibly modified variables (the output),
    and the third one the set of possibly raised exceptions.
 
    INVARIANTS: 
    1. there are no duplicate elements in each list 
    2. output is contained in input

    REMARK: for most operations, sets will be more relevant than lists,
    but order must not change when a substitution is applied and thus
    lists are preferred *)

type t = { 
  input : Ident.t list;
  output : Ident.t list;
  exns : Ident.set }

(*s the empty effect *)

let bottom = { input = []; output = []; exns = Idset.empty }

(*s basic operations *)

let list_add x l = if List.mem x l then l else x :: l

let list_remove x l = 
  let rec rem_rec = function
    | [] -> []
    | y :: l -> if x = y then l else y :: rem_rec l
  in
  if List.mem x l then rem_rec l else l

let mem x (r,w) = (List.mem x r) || (List.mem x w)

(* [list_union] is a merge sort *)
let list_union l1 l2 = 
  let rec basic_union = function
    | [], s2 -> s2
    | s1, [] -> s1
    | ((v1 :: l1) as s1), ((v2 :: l2) as s2) ->
	if v1 < v2 then
	  v1 :: basic_union (l1,s2)
	else if v1 > v2 then
	  v2 :: basic_union (s1,l2)
	else
	  v1 :: basic_union (l1,l2)
  in
  basic_union (List.sort compare l1, List.sort compare l2)

(*s adds reads and writes variables *)

let add_read x e = { e with input = list_add x e.input }

let add_reads = Idset.fold add_read

let add_write x e = 
  { input = list_add x e.input; output = list_add x e.output; exns = e.exns }

let add_writes = Idset.fold add_write

let add_exn x e = { e with exns = Idset.add x e.exns }

let add_exns = Idset.fold add_exn

(*s access *)

let get_reads e = e.input
let get_writes e = e.output
let get_exns e = Idset.elements e.exns
let get_repr e = e.input, e.output, Idset.elements e.exns

(*s tests *)

let is_read  e id = List.mem id e.input
let is_write e id = List.mem id e.output
let is_exn e id = Idset.mem id e.exns

let keep_writes e = { e with input = e.output }

(*s union and disjunction *)

let union e1 e2 =
  { input = list_union e1.input e2.input;
    output = list_union e1.output e2.output;
    exns = Idset.union e1.exns e2.exns }

(*s comparison relation *)

let le e1 e2 = failwith "effects: le: not yet implemented"

let inf e1 e2 = failwith "effects: inf: not yet implemented"

(*s remove *)

let remove x e = 
  { e with 
      input = list_remove x e.input;
      output = list_remove x e.output }

let remove_exn x e = { e with exns = Idset.remove x e.exns }

let erase_exns e = { e with exns = Idset.empty }

(*s occurrence *)

let occur x e = List.mem x e.input || List.mem x e.output

(*s substitution *)

let list_subst x x' l =
  let rec subst = function
    | [] -> []
    | y :: r -> if y = x then x' :: r else y :: subst r
  in
  if List.mem x l then subst l else l

let subst_one x x' e = 
  { e with input = list_subst x x' e.input; output = list_subst x x' e.output }

let subst = Idmap.fold subst_one

(*s pretty-print *)

open Format

(* copied to avoid circularity Effect <-> Misc *)
let rec print_list sep print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; sep fmt (); print_list sep print fmt r

let print fmt { input = r; output = w; exns = e } =
  fprintf fmt "@[";
  if r <> [] then begin
    fprintf fmt "reads ";
    print_list (fun fmt () -> fprintf fmt ",@ ") Ident.print fmt r;
  end;
  if r <> [] && w <> [] then fprintf fmt "@ ";
  if w <> [] then begin
    fprintf fmt "writes ";
    print_list (fun fmt () -> fprintf fmt ",@ ") Ident.print fmt w;
  end;
  let e = Idset.elements e in
  if w <> [] && e <> [] then fprintf fmt "@ ";
  if e <> [] then begin
    fprintf fmt "raises ";
    print_list (fun fmt () -> fprintf fmt ",@ ") Ident.print fmt e;
  end;
  if r <> [] || w <> [] || e <> [] then fprintf fmt "@ ";
  fprintf fmt "@]"

