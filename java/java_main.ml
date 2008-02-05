(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
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

(* $Id: java_main.ml,v 1.49 2008-02-05 20:24:05 nrousset Exp $ *)

open Java_env
open Java_ast
open Format


let main () =
  let files = Java_options.files () in
  try
    match files with
      | [] -> Java_options.usage ()
      | fl ->
	  (* phase 1 : parsing *)
	  let astl = List.map Java_syntax.file fl in
	    printf "Parsing OK.@.";
	    (* phase 2 : typing *)
	    Java_options.lprintf "(****** typing phase *****)@.";
	    let (p, t) = Java_typing.get_types [] astl in
	      Java_options.lprintf "(****** typing phase 2 : get bodies *****)@.";
	      List.iter (Java_typing.get_bodies p t) astl;
	      Java_options.lprintf "(****** typing phase 3 : type specs *****)@.";
	      Java_typing.type_specs p t;
	      printf "Typing OK.@.";
	      
	      (************)
	      (* Analyses *)
	      (************)
	      
	      Hashtbl.iter 
		(fun _ (f,t) -> Java_callgraph.compute_logic_calls f t)
		Java_typing.logics_table;
	      
	      Hashtbl.iter 
		(fun _ mt -> 
		   Option_misc.iter 
		     (Java_callgraph.compute_calls 
			mt.Java_typing.mt_method_info
			mt.Java_typing.mt_requires) 
		     mt.Java_typing.mt_body)
		Java_typing.methods_table;
	      
	      Hashtbl.iter 
		(fun _ ct -> 
		   Java_callgraph.compute_constr_calls 
		     ct.Java_typing.ct_constr_info
		     ct.Java_typing.ct_requires
		     ct.Java_typing.ct_body)
		Java_typing.constructors_table;
	      
	      let _logic_components = 
		Java_callgraph.compute_logic_components 
		  Java_typing.logics_table
	      in
	      let components = 
		Java_callgraph.compute_components 
		  Java_typing.methods_table
		  Java_typing.constructors_table
	      in
		Hashtbl.iter
		  (fun _ ty ->
		     Java_analysis.do_type ty)
		  Java_typing.type_table;
		(* analyze in any order *)
		(*
	Hashtbl.iter
	  (fun mi mti ->
	     Java_analysis.do_method 
	       mti.Java_typing.mt_method_info 
	       mti.Java_typing.mt_requires
	       mti.Java_typing.mt_ensures
	       mti.Java_typing.mt_behaviors 
	       mti.Java_typing.mt_body)
	  Java_typing.methods_table;
	Hashtbl.iter
	  (fun ci cti ->
	     Java_analysis.do_constructor 
	       cti.Java_typing.ct_constr_info 
	       cti.Java_typing.ct_requires
	       cti.Java_typing.ct_ensures
	       cti.Java_typing.ct_behaviors 
	       cti.Java_typing.ct_body)
	  Java_typing.constructors_table;
*)

	(* analyze following call graph order
	TODO: precise the meaning of call graph with dynamic calls *)
	Array.iter
	  (List.iter 
	    (fun mi -> 
	       match mi with
		 | MethodInfo mi -> 
		     let mti = Hashtbl.find Java_typing.methods_table
		       mi.method_info_tag
		     in
		     Java_analysis.do_method 
		       mti.Java_typing.mt_method_info 
		       mti.Java_typing.mt_requires
		       mti.Java_typing.mt_behaviors 
		       mti.Java_typing.mt_body
		 | ConstructorInfo ci ->
		     let cti = Hashtbl.find Java_typing.constructors_table
		       ci.constr_info_tag
		     in
		     Java_analysis.do_constructor
		       cti.Java_typing.ct_constr_info 
		       cti.Java_typing.ct_requires
		       cti.Java_typing.ct_behaviors 
		       cti.Java_typing.ct_body))
	    components;

	(*******************************)
	(* production of jessie output *)
	(*******************************)

(*
	(* production phase 1.1 : generation of Jessie logic types *)
	let decls_types =
	  Hashtbl.fold 
	    (fun _ id acc ->
	       Jc_interp.tr_logic_type id acc)
	    Jc_typing.logic_type_table
	    []
	in	       	  
*)
	(* production phase 1.2 : generation of Jessie range_types *)
	let decls_range = Java_interp.range_types [] in
	  
	(* production phase 1.3 : generation of Jessie struct types *)
	let non_null_preds, acc, decls_arrays = Java_interp.array_types [] in
	let acc, decls_structs =
	  Hashtbl.fold 
	    (fun _ id (acc0, acc) ->
	       Java_interp.tr_class_or_interface id acc0 acc)
	    Java_typing.type_table
	    (acc, decls_arrays)
	in

	(* production phase 1.4 : generation of Jessie logic functions *)
	let decls_fun = 
	  Hashtbl.fold 
	    (fun _ (li,p) acc ->
	       Java_interp.tr_logic_fun li p acc)
	    Java_typing.logics_table 
	    []
	in

	(* class invariants *)
	let acc = 
	  Hashtbl.fold
	    (fun _ (ci, id, invs) acc ->
	       Java_interp.tr_invariants ci id invs acc)
	    Java_typing.invariants_table acc
	in
	let decls = decls_fun @ decls_structs @ 
	  (Jc_output.JCrec_struct_defs acc :: decls_range)
	in
	let decls = decls @ non_null_preds in
	  
	(* production phase 1.5: generation of Jessie global invariants *)
	let decls =
	  Hashtbl.fold
	    (fun _ invs acc -> 
	       (List.map (Java_interp.tr_static_invariant) invs) @ acc)
	    Java_typing.static_invariants_table
	    decls
	in

	(* production phase 1.6 : generation of Jessie exceptions *)
	let decls =
	  Hashtbl.fold 
	    (fun _ ei acc ->
	       Java_interp.tr_exception ei acc)
	    Java_interp.exceptions_table
	    decls
	in	       	  

	(* production phase 3 : generation of Jessie axioms *)
	let decls = 
	  Hashtbl.fold 
	    (fun id (is_axiom,lab,p) acc ->
	       Java_interp.tr_axiom id is_axiom lab p acc)
	    Java_typing.axioms_table
	    decls
	in	       
	(* production phase 4 : generation of Jessie functions *)
	let decls =
	  Array.fold_left
	    (fun acc l ->
	       List.fold_left 
		 (fun acc f -> 
		    match f with
		      | MethodInfo mi -> 
			  let mt = Hashtbl.find Java_typing.methods_table
			    mi.method_info_tag
			  in
			  printf "Generating JC function %s for method %a.%s@." 
			    mi.method_info_trans_name
			    Java_typing.print_type_name 
			    mi.method_info_class_or_interface
			    mi.method_info_name;
			  Java_interp.tr_method mi 
			    mt.Java_typing.mt_requires 
			    mt.Java_typing.mt_behaviors 
			    mt.Java_typing.mt_body acc
		      | ConstructorInfo ci ->
			  let ct = Hashtbl.find Java_typing.constructors_table
			    ci.constr_info_tag
			  in
			  printf "Generating JC function %s for constructor %s@." 
			    ci.constr_info_trans_name
			    ci.constr_info_class.class_info_name;
			  Java_interp.tr_constr ci 
			    ct.Java_typing.ct_requires 
			    ct.Java_typing.ct_behaviors 
			    ct.Java_typing.ct_body acc)
		 acc
		 l)
	    decls
	    components
	in

	(*
	  let decls = 
	  Hashtbl.fold 
	  (fun _ ct acc ->
	  let f = ct.Java_typing.ct_constr_info in
	  printf "Generating Why function %s@." 
	  f.Java_env.constr_info_class.class_info_name;
	  Java_interp.tr_constr f ct.Java_typing.ct_requires 
		    ct.Java_typing.ct_behaviors 
	   ct.Java_typing.ct_body acc)
	    Java_typing.constructors_table
	  decls
	  in	       
	  let decls = 
	  Hashtbl.fold 
	    (fun _ mt acc ->
	  let f = mt.Java_typing.mt_method_info in
	  printf "Generating Why function %s@." 
	  f.Java_env.method_info_name;
	        Java_interp.tr_method f 
	         mt.Java_typing.mt_requires 
  		 mt.Java_typing.mt_ensures
  		 mt.Java_typing.mt_behaviors 
	  mt.Java_typing.mt_body acc)
	  Java_typing.methods_table
	  decls
	  in	       
	*)

	(* production phase 5 : produce Jessie file *)
	let decls = Jc_output.JCinvariant_policy !Java_options.inv_sem 
	  :: Jc_output.JCannotation_policy !Java_options.annotation_sem
	  :: Jc_output.JCabstract_domain !Java_options.ai_domain
	  :: List.rev decls 
	in
	let f = List.hd fl in
	let f = Filename.chop_extension f in
	let cout = Pp.print_in_file_no_close
	  (fun fmt -> fprintf fmt "%a@." Jc_output.print_decls decls)
	  (f ^ ".jc") 
	in
	output_string cout "/*\n";
	output_string cout "Local"; 
	(* splitted because confuses Emacs otherwise *)
	output_string cout "Variables:\n";
	output_string cout "mode: java\n";
	output_string cout "compile-command: \"jessie -why-opt -split-user-conj -locs ";
	output_string cout f;
	output_string cout ".jloc ";
	output_string cout f;
	output_string cout ".jc && make -f ";
	output_string cout f;
	output_string cout ".makefile gui\"\n";
	output_string cout "End:\n";
	output_string cout "*/\n";
	close_out cout;

	(* production phase 5.2 : produce locs file *)
	Pp.print_in_file Output.print_locs (Lib.file "." (f ^ ".jloc"));

	printf "Done.@."

  with
    | Java_typing.Typing_error(l,s) ->
	eprintf "%a: typing error: %s@." Loc.gen_report_position l s;
	exit 1
    | Java_options.Java_error(l,s) ->
	eprintf "%a: %s@." Loc.gen_report_position l s;
	exit 1


let _ = 
  Sys.catch_break true;
  try
    main ()
  with
      (Assert_failure _ | Match_failure _ ) as exc -> 
	eprintf "%s@." (Printexc.to_string exc);
	exit 2


(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/krakatoa.byte"
End: 
*)

