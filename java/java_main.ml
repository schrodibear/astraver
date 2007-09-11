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
	Java_typing.get_types ast;
	Java_typing.get_prototypes ast;
	Java_typing.get_bodies ast;
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

	(************)
	(* Analyses *)
	(************)

	Hashtbl.iter 
	  (fun _ (f,t) -> Java_callgraph.compute_logic_calls f t)
	  Java_typing.logics_table;
	Hashtbl.iter 
	  (fun _ mt -> 
	     Option_misc.iter (Java_callgraph.compute_calls 
				 mt.Java_typing.mt_method_info
				 mt.Java_typing.mt_requires) 
	       mt.Java_typing.mt_body)
	  Java_typing.methods_table;
	let _logic_components = 
	  Java_callgraph.compute_logic_components 
	    Java_typing.logics_table
	in
	let components = 
	  Java_callgraph.compute_components 
	    Java_typing.methods_table
	in
	(* analyze following call graph order *)
	Array.iter
	  (List.iter 
	    (fun mi -> 
	       let mti = Hashtbl.find Java_typing.methods_table
		 mi.method_info_tag
	       in
	       Java_analysis.do_method 
		 mti.Java_typing.mt_method_info 
		 mti.Java_typing.mt_requires
		 mti.Java_typing.mt_behaviors 
		 mti.Java_typing.mt_body))
	    components;

	(*******************************)
	(* production of jessie output *)
	(*******************************)

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
	let decls = Java_interp.array_types decls in
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
	(* production phase 1.5 : generation of Jessie logic functions *)
	let decls = 
	  Hashtbl.fold 
	    (fun _ (li,p) acc ->
	       Java_interp.tr_logic_fun li p acc)
	    Java_typing.logics_table 
	    decls
	in
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
	    (fun _ mt acc ->
	       let f = mt.Java_typing.mt_method_info in
	       printf "Generating Why function %s@." 
		 f.Java_env.method_info_name;
	       Java_interp.tr_method f mt.Java_typing.mt_requires 
		 mt.Java_typing.mt_behaviors 
		 mt.Java_typing.mt_body acc)
	    Java_typing.methods_table
	    decls
	in	       
	(* production phase 5 : produce Jessie file *)
	let decls = List.rev decls in
	let f = Filename.chop_extension f in
	let cout = Pp.print_in_file_no_close
	  (fun fmt -> fprintf fmt "%a@." Jc_output.print_decls decls)
	  (f ^ ".jc") 
	in
	output_string cout "/*\n";
	output_string cout "Local Variables:\n";
	output_string cout "mode: java\n";
	output_string cout "compile-command: \"jessie -why-opt -split-user-conj";
	output_string cout f;
	output_string cout ".jc ; make -f ";
	output_string cout f;
	output_string cout ".makefile gui\"\n";
	output_string cout "End:\n";
	output_string cout "*/\n";
	close_out cout;
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
  Printexc.catch main ()

  
(*
Local Variables: 
compile-command: "make -j -C .. bin/krakatoa.byte"
End: 
*)
