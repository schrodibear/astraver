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
	(* phase 2 : typing *)
	Java_typing.compilation_unit ast;
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
	(* production phase 1.3 : generation of Why exceptions *)
	let d_exc =
	  Hashtbl.fold 
	    (fun _ ei acc ->
	       Jc_interp.tr_exception ei acc)
	    Jc_typing.exceptions_table
	    d_memories
	in	       	  
	(* production phase 1.4 : generation of Why range_types *)
	let d_range =
	  Hashtbl.fold 
	    (fun _ (ri,to_int,to_int_,of_int) acc ->
	       Jc_interp.tr_range_type ri to_int_ of_int acc)
	    Jc_typing.range_types_table
	    d_exc
	in	       	  
	(* production phase 2 : generation of Why logic functions *)
	let d_lfuns = 
	  Hashtbl.fold 
	    (fun _ (li,p) acc ->
	       Jc_interp.tr_logic_fun li p acc)
	    Jc_typing.logic_functions_table 
	    d_range
	in
	(* production phase 3 : generation of Why axioms *)
	let d_axioms = 
	  Hashtbl.fold 
	    (fun id p acc ->
	       Jc_interp.tr_axiom id p acc)
	    Jc_typing.axioms_table
	    d_lfuns
	in	       
	(* production phase 4 : generation of Why functions *)
	let d_funs = 
	  Hashtbl.fold 
	    (fun _ (f,s,b) acc ->
	       printf "Generating Why function %s@." 
		 f.Jc_fenv.jc_fun_info_name;
	       Jc_interp.tr_fun f s b acc)
	    Jc_typing.functions_table
	    d_axioms
	in	       
	(* production phase 5 : produce Why file *)
	let f = Filename.chop_extension f in
	Pp.print_in_file 
	  (fun fmt -> fprintf fmt "%a@." Output.fprintf_why_decls d_funs)
	  (Lib.file "why" (f ^ ".why"));
	(* phase x : produce makefile *)
	Jc_make.makefile f
*)
	printf "Parsing OK.@."

    | _ -> Java_options.usage ()
    
  with
(*
    | Java_typing.Typing_error(l,s) ->
	eprintf "%a: typing error: %s@." Loc.gen_report_position l s;
	exit 1
*)
    | Java_options.Java_error(l,s) ->
	eprintf "%a: %s@." Loc.gen_report_position l s;
	exit 1


let _ = Printexc.catch main ()

  
(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
