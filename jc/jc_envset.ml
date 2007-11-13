(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(* $Id: jc_envset.ml,v 1.10 2007-11-13 15:37:55 moy Exp $ *)

open Jc_env

module StringSet = Set.Make(String)

module StringMap = Map.Make(String)

(* used names (in order to rename identifiers when necessary) *)
let used_names = Hashtbl.create 97

let mark_as_used x = 
  Hashtbl.add used_names x ()

let () = 
  List.iter mark_as_used 
    [ (* Why keywords *)
      "absurd"; "and"; "array"; "as"; "assert"; "axiom"; "begin";
      "bool"; "do"; "done"; "else"; "end"; "exception"; "exists";
      "external"; "false"; "for"; "forall"; "fun"; "function"; "goal";
      "if"; "in"; "int"; "invariant"; "label"; "let"; "logic"; "not";
      "of"; "or"; "parameter"; "predicate"; "prop"; "raise"; "raises";
      "reads"; "real"; "rec"; "ref"; "result"; "returns"; "then"; "true"; "try";
      "type"; "unit"; "variant"; "void"; "while"; "with"; "writes" ;
      (* jessie generated names *)
      (* "global" ; "alloc"  *)
    ]

let is_used_name n = Hashtbl.mem used_names n

let use_name ?local_names n = 
  if is_used_name n then raise Exit; 
  begin match local_names with 
    | Some h -> if StringSet.mem n h then raise Exit 
    | None -> () 
  end;
  mark_as_used n;
  n

let rec next_name ?local_names n i = 
  let n_i = n ^ "_" ^ string_of_int i in
  try use_name ?local_names n_i 
  with Exit -> next_name ?local_names n (succ i)

let get_unique_name ?local_names n = 
  try use_name ?local_names n 
  with Exit -> next_name ?local_names n 0


module VarSet = 
  Set.Make(struct type t = var_info
		  let compare v1 v2 = 
		    Pervasives.compare 
		      v1.jc_var_info_tag v2.jc_var_info_tag
	   end)

module FieldOrd =
  struct type t = field_info
	 let compare f1 f2 = 
	   Pervasives.compare 
	     f1.jc_field_info_tag f2.jc_field_info_tag
  end

module FieldSet = Set.Make(FieldOrd)

module FieldMap = Map.Make(FieldOrd)

module ExceptionOrd =   
  struct type t = exception_info
	 let compare f1 f2 = 
	   Pervasives.compare 
	     f1.jc_exception_info_tag f2.jc_exception_info_tag
  end

module ExceptionSet = Set.Make(ExceptionOrd)

module ExceptionMap = Map.Make(ExceptionOrd)


(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
