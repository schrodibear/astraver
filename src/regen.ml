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

(*i $Id: regen.ml,v 1.8 2004-02-23 17:14:58 filliatr Exp $ i*)

(* files partly edited and partly regenerated *)

open Format
open Options
open Cc
open Logic
open Vcg
open Misc

type element_kind = 
  | Param
  | Oblig
  | Valid (* obsolete but helps porting from old versions *)
  | Lg
  | Ax

type element_id = element_kind * string

type element = 
  | Parameter of string * cc_type
  | Obligation of obligation
  | Logic of string * logic_type
  | Axiom of string * predicate

module type S = sig
 
  (* how to print and reprint elements *)
  val print_element : formatter -> element -> unit
  val reprint_element : formatter -> element -> unit

  (* regexp to recognize obligations locations (as comments) *)
  val re_oblig_loc : Str.regexp

  (* what to print at the beginning of file when first created *)
  val first_time : formatter -> unit

  (* how to recognize the end of an element to erase / overwrite *)
  val not_end_of_element : element_id -> string -> bool

end

module Make(X : S) = struct

  let print_element_kind fmt = function
    | Param, s -> fprintf fmt "parameter %s" s
    | Oblig, s -> fprintf fmt "obligation %s" s
    | Valid, s -> fprintf fmt "validation %s" s
    | Lg, s -> fprintf fmt "logic %s" s
    | Ax, s -> fprintf fmt "axiom %s" s

  let elem_t = Hashtbl.create 97 (* maps [element_id] to [element] *)
  let elem_q = Queue.create ()   (* queue of [element_id * element] *)
		 
  let add_elem ek e = Queue.add (ek,e) elem_q; Hashtbl.add elem_t ek e
    
  let reset () = Queue.clear elem_q; Hashtbl.clear elem_t

  let regexps = ref []
		  
  let add_regexp r k = regexps := (Str.regexp r, k) :: !regexps

  type line_kind =
    | Obligation_location
    | Element of (element_kind * string)
    | Other

  let check_line s =
    let rec test = function
      | [] -> 
	  Other
      | (r, k) :: l ->
	  if Str.string_match r s 0 then 
	    Element (k, Str.matched_group 1 s) 
	  else 
	    test l
    in
    if Str.string_match X.re_oblig_loc s 0 then 
      Obligation_location
    else
      test !regexps
	
  let regen oldf fmt =
    let cin = open_in oldf in
    let rec scan () =
      let s = input_line cin in
      match check_line s with
	| Other -> 
	    fprintf fmt "%s@\n" s;
	    scan ()
	| Obligation_location ->
	    scan ()
	| Element e ->
	    if Hashtbl.mem elem_t e then begin
	      if verbose then eprintf "overwriting %a@." print_element_kind e;
	      print_up_to e
	    end else
	      if verbose then eprintf "erasing %a@." print_element_kind e;
	    if X.not_end_of_element e s then skip_element e;
	    scan ()
    and skip_element e =
      let s = input_line cin in
      if X.not_end_of_element e s then skip_element e
    and tail () = 
      fprintf fmt "%c" (input_char cin); tail () 
    and print_up_to e =
      let (e',ee) = Queue.take elem_q in
      Hashtbl.remove elem_t e'; 
      if e = e' then 
	X.reprint_element fmt ee 
      else begin
	X.print_element fmt ee; print_up_to e
      end
    in
    begin
      try scan () with End_of_file -> 
      try tail () with End_of_file -> close_in cin
    end;
    Queue.iter (fun (_,e) -> X.print_element fmt e) elem_q

  let first_time fmt =
    X.first_time fmt;
    Queue.iter (fun (_,e) -> X.print_element fmt e) elem_q

  let output_file margin f =
    if Sys.file_exists f then begin
      let fbak = f ^ ".bak" in
      Sys.rename f fbak; 
      if_verbose_3 eprintf "*** re-generating file %s (backup in %s)@." f fbak;
      print_in_file margin (regen fbak) f
    end else begin
      if_verbose_2 eprintf "*** generating file %s@." f;
      print_in_file margin first_time f
    end

end
