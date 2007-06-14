open Java_env
open Java_ast
open Format


let main () =
  let files = Java_options.files () in
  try
    match files with
    | [f] ->
	(* phase 1 : parsing *)
	let ast = Java_syntax.file f in
	printf "Parsing OK.@.";
	(* phase 2 : typing *)
	Java_typing.compilation_unit ast;
	printf "Typing OK.@.";
(*
	(* phase 3 : computation of call graph *)
	Hashtbl.iter 
	  (fun _ (f,t) -> Jc_callgraph.compute_logic_calls f t)
	  Jc_typing.logic_functions_table;
	Hashtbl.iter 
	  (fun _ (f,s,b) -> Jc_callgraph.compute_calls f s b)
	  Jc_typing.functions_table;
	let logic_components = 
	  Jc_callgraph.compute_logic_components 
	    Jc_typing.logic_functions_table
	in
	let components = 
	  Jc_callgraph.compute_components Jc_typing.functions_table
	in
	(* phase 4 : computation of effects *)
	Jc_options.lprintf "\nstarting computation of effects of logic functions.@.";
	Array.iter Jc_effect.logic_effects logic_components;
	Jc_options.lprintf "\nstarting computation of effects of functions.@.";
	Array.iter Jc_effect.function_effects components;
	(* phase 5 : checking structure invariants *)
	Jc_options.lprintf "\nstarting checking structure invariants.@.";
	Hashtbl.iter 
	  (fun _ (_,invs) -> Jc_invariants.check invs)
	  Jc_typing.structs_table;
*)
	let decls = [] in
(*
	(* production phase 1.1 : generation of Jessie logic types *)
	let d_types =
	  Hashtbl.fold 
	    (fun _ id acc ->
	       Jc_interp.tr_logic_type id acc)
	    Jc_typing.logic_type_table
	    []
	in	       	  
*)
	(* production phase 1.2 : generation of Jessie range_types *)
	let decls = Java_interp.range_types decls in
	(* production phase 1.3 : generation of Jessie struct types *)
	let decls =
	  Hashtbl.fold 
	    (fun _ id acc ->
	       Java_interp.tr_class id acc)
	    Java_typing.class_table
	    decls
	in	
(*       	  
	(* production phase 1.4 : generation of Jessie exceptions *)
	let d_exc =
	  Hashtbl.fold 
	    (fun _ ei acc ->
	       Jc_interp.tr_exception ei acc)
	    Jc_typing.exceptions_table
	    d_memories
	in	       	  
*)
(*
	(* production phase 2 : generation of Jessie logic functions *)
	let d_lfuns = 
	  Hashtbl.fold 
	    (fun _ (li,p) acc ->
	       Jc_interp.tr_logic_fun li p acc)
	    Jc_typing.logic_functions_table 
	    d_range
	in
*)
	(* production phase 3 : generation of Jessie axioms *)
	let decls = 
	  Hashtbl.fold 
	    (fun id p acc ->
	       Java_interp.tr_axiom id p acc)
	    Java_typing.axioms_table
	    decls
	in	       
	(* production phase 4 : generation of Jessie functions *)
	let decls = 
	  Hashtbl.fold 
	    (fun _ (f,req,behs,body) acc ->
	       printf "Generating Why function %s@." 
		 f.Java_env.method_info_name;
	       Java_interp.tr_method f req behs body acc)
	    Java_typing.methods_table
	    decls
	in	       
	(* production phase 5 : produce Jessie file *)
	let decls = List.rev decls in
	let f = Filename.chop_extension f in
	Pp.print_in_file 
	  (fun fmt -> fprintf fmt "%a@." Jc_output.print_decls decls)
	  (f ^ ".jc");
	(* phase x : produce makefile *)
(*
	Java_make.makefile f
*)
	printf "Done.@."

    | _ -> Java_options.usage ()
    
  with
    | Java_typing.Typing_error(l,s) ->
	eprintf "%a: typing error: %s@." Loc.gen_report_position l s;
	exit 1
    | Java_options.Java_error(l,s) ->
	eprintf "%a: %s@." Loc.gen_report_position l s;
	exit 1


let _ = 
  Sys.catch_break true;
  (* Printexc.catch *) main ()

  
(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
