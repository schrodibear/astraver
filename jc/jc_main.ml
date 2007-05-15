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
	(* phase 3 : normalization *)
	Hashtbl.iter (fun tag x -> 
			Hashtbl.add Jc_norm.logic_type_table tag x)
	  Jc_typing.logic_type_table;
	Hashtbl.iter 
	  (fun tag (f,t) -> 
	     let t = Jc_norm.logic_function t in
	     Hashtbl.add Jc_norm.logic_functions_table tag (f,t))
	  Jc_typing.logic_functions_table;
	Hashtbl.iter 
	  (fun tag (f,s,b) -> 
	     let (s,b) = Jc_norm.code_function (s,b) in
	     Hashtbl.add Jc_norm.functions_table tag (f,s,b))
	  Jc_typing.functions_table;
	Hashtbl.iter 
	  (fun tag (si,l) -> 
	     let l = List.map (fun (li, a) -> (li, Jc_norm.assertion a)) l in
	     Hashtbl.add Jc_norm.structs_table tag (si,l))
	  Jc_typing.structs_table;
	Hashtbl.iter (fun tag x -> 
			Hashtbl.add Jc_norm.range_types_table tag x)
	  Jc_typing.range_types_table;
	Hashtbl.iter 
	  (fun tag a -> 
	     let a = Jc_norm.assertion a in
	     Hashtbl.add Jc_norm.axioms_table tag a)
	  Jc_typing.axioms_table;
	Hashtbl.iter (fun tag x -> 
			Hashtbl.add Jc_norm.exceptions_table tag x)
	  Jc_typing.exceptions_table;	

	  
	(* phase 4 : computation of call graph *)
	Hashtbl.iter 
	  (fun _ (f,t) -> Jc_callgraph.compute_logic_calls f t)
	  Jc_norm.logic_functions_table;
	Hashtbl.iter 
	  (fun _ (f,s,b) -> Jc_callgraph.compute_calls f s b)
	  Jc_norm.functions_table;
	let logic_components = 
	  Jc_callgraph.compute_logic_components 
	    Jc_norm.logic_functions_table
	in
	let components = 
	  Jc_callgraph.compute_components Jc_norm.functions_table
	in
	(* phase 5 : computation of effects *)
	Jc_options.lprintf "\nstarting computation of effects of logic functions.@.";
	Array.iter Jc_effect.logic_effects logic_components;
	Jc_options.lprintf "\nstarting computation of effects of functions.@.";
	Array.iter Jc_effect.function_effects components;
	(* phase 6 : checking structure invariants *)
	(* --- DISABLED ---
	Jc_options.lprintf "\nstarting checking structure invariants.@.";
	Hashtbl.iter 
	  (fun _ (_,invs) -> Jc_invariants.check invs)
	  Jc_norm.structs_table; *)

	(* production phase 1.1 : generation of Why logic types *)
	let d_types =
	  Hashtbl.fold 
	    (fun _ id acc ->
	       Jc_interp.tr_logic_type id acc)
	    Jc_norm.logic_type_table
	    []
	in	       	 
	(* production phase 1.2.1 : generation of Why memories *)
	let d_memories =
	  Hashtbl.fold 
	    (fun _ (st,_) acc ->
	       Jc_interp.tr_struct st acc)
	    Jc_norm.structs_table
	    d_types
	in	       	  
	(* production phase 1.2.2 : generation of the inv predicates for structures *)
        let d_inv =
	  Hashtbl.fold 
	    (fun _ (st,_) acc ->
	       Jc_interp.tr_valid_inv st acc)
	    Jc_norm.structs_table
	    d_memories
	in
	let d_inv = Jc_interp.assoc_declaration::d_inv in
        let d_inv =
          Hashtbl.fold
            (fun _ (st, _) acc ->
               Jc_interp.invariants_axioms st acc)
            Jc_norm.structs_table
            d_inv
        in
	(* production phase 1.3 : generation of Why exceptions *)
	let d_exc =
	  Hashtbl.fold 
	    (fun _ ei acc ->
	       Jc_interp.tr_exception ei acc)
	    Jc_norm.exceptions_table
	    d_inv (* d_memories *)
	in	       	  
	(* production phase 1.4 : generation of Why range_types *)
	let d_range =
	  Hashtbl.fold 
	    (fun _ (ri,to_int,to_int_,of_int) acc ->
	       Jc_interp.tr_range_type ri to_int_ of_int acc)
	    Jc_norm.range_types_table
	    d_exc
	in	       	  
	(* production phase 2 : generation of Why logic functions *)
	let d_lfuns = 
	  Hashtbl.fold 
	    (fun _ (li,p) acc ->
	       Jc_interp.tr_logic_fun li p acc)
	    Jc_norm.logic_functions_table 
	    d_range
	in
	(* production phase 3 : generation of Why axioms *)
	let d_axioms = 
	  Hashtbl.fold 
	    (fun id p acc ->
	       Jc_interp.tr_axiom id p acc)
	    Jc_norm.axioms_table
	    d_lfuns
	in	       
	(* production phase 4 : generation of Why functions *)
	let d_funs = 
	  Hashtbl.fold 
	    (fun _ (f,s,b) acc ->
	       printf "Generating Why function %s@." 
		 f.Jc_fenv.jc_fun_info_name;
	       Jc_interp.tr_fun f s b acc)
	    Jc_norm.functions_table
	    d_axioms
	in	       
	(* production phase 5 : produce Why file *)
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
