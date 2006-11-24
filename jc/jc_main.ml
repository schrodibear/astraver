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

open Jc_env
open Jc_ast
open Format

let parse_file f = 
  try
    let c = open_in f in
    let d = Jc_lexer.parse f c in
    close_in c; d
  with
    | Jc_lexer.Lexical_error(l,s) ->
	eprintf "%a: lexical error: %s@." Loc.gen_report_position l s;
	exit 1


let main () =
  let files = Jc_options.files () in
  try
    match files with
    | [f] ->
	(* phase 1 : parsing *)
	let ast = parse_file f in
	(* phase 2 : typing *)
	List.iter Jc_typing.decl ast;
	(* phase 3 : computation of call graph *)
	Hashtbl.iter 
	  (fun _ (f,s,b) -> Jc_callgraph.compute_calls f s b)
	  Jc_typing.functions_table;
	let components = 
	  Jc_callgraph.compute_components Jc_typing.functions_table
	in
	(* phase 4 : computation of effects *)
	Jc_options.lprintf "\nstarting computation of effects.@.";
	Array.iter Jc_effect.function_effects components;
	(* phase 5 : checking structure invariants *)
	Jc_options.lprintf "\nstarting checking structure invariants.@.";
	Hashtbl.iter 
	  (fun _ (_,invs) -> Jc_invariants.check invs)
	  Jc_typing.structs_table;
	(* production phase 1 : generation of Why memories *)
	let d_memories =
	  Hashtbl.fold 
	    (fun _ (st,invs) acc ->
	       Jc_interp.tr_struct st invs acc)
	    Jc_typing.structs_table
	    []
	in	       	  
	(* production phase 2 : generation of Why axioms *)
	let d_axioms = 
	  Hashtbl.fold 
	    (fun id p acc ->
	       Jc_interp.tr_axiom id p acc)
	    Jc_typing.axioms_table
	    d_memories
	in	       
	(* production phase 3 : generation of Why functions *)
	let d_funs = 
	  Hashtbl.fold 
	    (fun _ (f,s,b) acc ->
	       printf "Generating Why function %s@." 
		 f.Jc_fenv.jc_fun_info_name;
	       Jc_interp.tr_fun f s b acc)
	    Jc_typing.functions_table
	    d_axioms
	in	       
	(* production phase 4 : produce Why file *)
	let f = Filename.chop_extension f in
	Pp.print_in_file 
	  (fun fmt -> fprintf fmt "%a@." Output.fprintf_why_decls d_funs)
	  (Lib.file "why" (f ^ ".why"));
	(* phase x : produce makefile *)
	Jc_make.makefile f


    | _ -> Jc_options.usage ()
    
  with
    | Jc_typing.Typing_error(l,s) ->
	eprintf "%a: typing error: %s@." Loc.gen_report_position l s;
	exit 1
    | Jc_options.Jc_error(l,s) ->
	eprintf "%a: %s@." Loc.gen_report_position l s;
	exit 1


let _ = Printexc.catch main ()

  
(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
