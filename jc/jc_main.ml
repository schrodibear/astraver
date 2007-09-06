(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
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
open Jc_fenv
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
(*
	Hashtbl.iter (fun tag x -> 
			Hashtbl.add Jc_typing.logic_type_table tag x)
	  Jc_typing.logic_type_table;
	Hashtbl.iter 
	  (fun tag (f,t) -> 
	     Hashtbl.add Jc_norm.logic_functions_table tag (f,t))
	  Jc_typing.logic_functions_table;
*)
	Hashtbl.iter 
	  (fun tag (f,s,b) -> 
	     let (s,b) = Jc_norm.code_function (s,b) in
	     Hashtbl.add Jc_norm.functions_table tag (f,s,b))
	  Jc_typing.functions_table;
	Hashtbl.iter 
	  (fun tag (v,e) -> 
	     let (v,e) = Jc_norm.static_variable (v,e) in
	     Hashtbl.add Jc_norm.variables_table tag (v,e))
	  Jc_typing.variables_table;
(*
	Hashtbl.iter 
	  (fun tag (si,l) -> 
	     let l = List.map (fun (li, a) -> (li, Jc_norm.assertion a)) l in
	     Hashtbl.add Jc_norm.structs_table tag (si,l))
	  Jc_typing.structs_table;
*)
(*
	Hashtbl.iter (fun tag x -> 
			Hashtbl.add Jc_norm.enum_types_table tag x)
	  Jc_typing.enum_types_table;
*)
(*
	Hashtbl.iter 
	  (fun tag a -> 
	     let a = Jc_norm.assertion a in
	     Hashtbl.add Jc_norm.axioms_table tag a)
	  Jc_typing.axioms_table;
*)
(*
	Hashtbl.iter (fun tag x -> 
			Hashtbl.add Jc_norm.exceptions_table tag x)
	  Jc_typing.exceptions_table;	
*)	  
	  
	(* phase 4 : computation of call graph *)
	Hashtbl.iter 
	  (fun _ (f,t) -> Jc_callgraph.compute_logic_calls f t)
	  Jc_typing.logic_functions_table;
	Hashtbl.iter 
	  (fun _ (f,s,b) -> 
	     Option_misc.iter (Jc_callgraph.compute_calls f s) b)
	  Jc_norm.functions_table;
	let logic_components = 
	  Jc_callgraph.compute_logic_components 
	    Jc_typing.logic_functions_table
	in
	let components = 
	  Jc_callgraph.compute_components Jc_norm.functions_table
	in

        (* phase 4.1 (optional) : inference of annotations *)
(* Yannick
	if Jc_options.annot_infer then
	  Hashtbl.iter 
	    (fun _ (f,s,b) -> 
	      Jc_annot_inference.code_function (f,s,b) 
	    ) Jc_norm.functions_table;
Yannick *)

	if Jc_options.ai_domain <> "" then
	  begin
	    if Jc_options.verbose then printf "Begin AI@.";
	    Hashtbl.iter 
	      (fun tag (fi, fs, bo) ->
		if Jc_options.main = "" then
		  (* no main: inference of loop invariants only *)
		  let bo = Jc_ai.code_function fi bo in
		  Hashtbl.replace Jc_norm.functions_table tag (fi, fs, bo)
		else
		  if fi.jc_fun_info_name = Jc_options.main then
		    (* main: inference of pre/post and loop invariants *)
		    Jc_ai.main_function fi fs bo
		  else
		    ())
	      Jc_norm.functions_table;
	    if Jc_options.verbose then printf "End AI@."
	  end;
	
	(* phase 5 : computation of effects *)
	Jc_options.lprintf "\nstarting computation of effects of logic functions.@.";
	Array.iter Jc_effect.logic_effects logic_components;
	Jc_options.lprintf "\nstarting computation of effects of functions.@.";
	Array.iter Jc_effect.function_effects components;

	(* phase 6 : checking structure invariants *)
	Jc_options.lprintf "\nstarting checking structure invariants.@.";
	Hashtbl.iter 
	  (fun _ (_,invs) -> Jc_invariants.check invs)
	  Jc_typing.structs_table;

	(* production phase 1.1 : generation of Why logic types *)
	let d_types =
	  Hashtbl.fold 
	    (fun _ id acc ->
	       Jc_interp.tr_logic_type id acc)
	    Jc_typing.logic_type_table
	    []
	in	       	 
	(* production phase 1.2 : generation of Why memories *)
	let d_memories =
	  Hashtbl.fold 
	    (fun _ (st,_) acc ->
	       Jc_interp.tr_struct st acc)
	    Jc_typing.structs_table
	    d_types
	in	       	  
	let d_memories =
	  Hashtbl.fold 
	    (fun _ (v,e) acc ->
	       Jc_interp.tr_variable v e acc)
	    Jc_norm.variables_table
	    d_memories
	in	       	  
	(* production phase 1.3 : generation of Why exceptions *)
	let d_exc =
	  Hashtbl.fold 
	    (fun _ ei acc ->
	       Jc_interp.tr_exception ei acc)
	    Jc_typing.exceptions_table
	    d_memories
	in	       	  
	(* production phase 1.4 : generation of Why enum_types *)
	let d =
	  Hashtbl.fold 
	    (fun _ (ri (* ,to_int,to_int_,of_int *)) acc ->
	       Jc_interp.tr_enum_type ri (* to_int_ of_int *) acc)
	    Jc_typing.enum_types_table
	    d_exc
	in	       	  
	(* production phase x.x : generation of Why logic constants *)
	let d =
	  Hashtbl.fold 
	    (fun _ (vi,init) acc ->
	       Jc_interp.tr_logic_const vi init acc)
	    Jc_typing.logic_constants_table
	    d
	in	       	  
	(* production phase 2 : generation of Why logic functions *)
	let d_lfuns = 
	  Hashtbl.fold 
	    (fun _ (li,p) acc ->
	       Jc_interp.tr_logic_fun li p acc)
	    Jc_typing.logic_functions_table 
	    d
	in
	(* production phase 3 : generation of Why axioms *)
	let d_axioms = 
	  Hashtbl.fold 
	    (fun id p acc ->
	       Jc_interp.tr_axiom id p acc)
	    Jc_typing.axioms_table
	    d_lfuns
	in	       
	(* production phase 3.5 : generation of global invariant predicates *)
	let d_axioms = Jc_invariants.make_global_invariants d_axioms in
	Jc_options.lprintf "production phase 4 : generation of Why functions@.";
	let d_funs = 
	  Hashtbl.fold 
	    (fun _ (f,s,b) acc ->
	       printf "Generating Why function %s@." 
		 f.Jc_fenv.jc_fun_info_name;
	       Jc_interp.tr_fun f s b acc)
	    Jc_norm.functions_table
	    d_axioms
	in	       
	Jc_options.lprintf "production phase 5 : (invariants tools)@.";
	let d_inv = d_funs in
	(* production phase 5.1 : "assoc" declaration *)
	(*let d_inv = Jc_invariants.assoc_declaration::d_funs in *)
	(* production phase 5.2 : "mutable" and "committed" declarations *)
	let d_inv =
          Hashtbl.fold
            (fun _ (st, _) acc ->
               Jc_invariants.mutable_declaration st acc)
            Jc_typing.structs_table
            d_inv
        in
	(* production phase 5.3 : global invariants (not mutable implies invariant) *)
        (*let d_inv =
          Hashtbl.fold
            (fun _ (st, _) acc ->
               Jc_invariants.invariants_axioms st acc)
            Jc_norm.structs_table
            d_inv
        in*)
	(* production phase 5.4 : pack *)
        let d_inv =
          Hashtbl.fold
            (fun _ (st, _) acc ->
               Jc_invariants.pack_declaration st acc)
            Jc_typing.structs_table
            d_inv
        in
	(* production phase 5.5 : unpack *)
        let d_inv =
          Hashtbl.fold
            (fun _ (st, _) acc ->
               Jc_invariants.unpack_declaration st acc)
            Jc_typing.structs_table
            d_inv
        in
	(* production phase 6.1 : produce Why file *)
	let f = Filename.chop_extension f in
	Pp.print_in_file 
	  (fun fmt -> fprintf fmt "%a@." Output.fprintf_why_decls d_inv)
	  (Lib.file "why" (f ^ ".why"));
	(* production phase 6.2 : produce locs file *)
	Pp.print_in_file 
	  Jc_interp.print_locs
	  (Lib.file "." (f ^ ".loc"));
	(* production phase 6.3 : produce makefile *)
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
