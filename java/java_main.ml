(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



open Java_env
open Java_ast
open Format
open Jc_constructors.PDecl

let main () =
  let files = Java_options.files () in
  if files = [] then Java_options.usage ();
  (* phase 1 : parsing *)
  let astl = List.map Java_syntax.file files in
  printf "Parsing OK.@.";
  (* phase 2 : typing *)
  Java_options.lprintf "(****** typing phase *****)@.";
  let (p, t) = Java_typing.get_types [] astl in
  Java_options.lprintf "(****** typing phase 2 : get bodies *****)@.";
  List.iter (Java_typing.get_bodies p t) astl;
  Java_options.lprintf "(****** typing phase 3 : type specs *****)@.";
  Java_typing.type_specs p t;
  printf "Typing OK.@.";

  if !Java_options.abstract <> "" then
    begin
      match astl with
	| [a] ->
	    Pp.print_in_file
	      (fun fmt -> Java_abstract.compilation_unit fmt a)
	      !Java_options.abstract;
	    exit 0
	| _ ->
	    eprintf "cannot take %d files with option -abstract@." (List.length astl);
	    Java_options.usage ()
    end;

  (************)
  (* Analyses *)
  (************)

  Hashtbl.iter
    (fun _ (f,t) -> Java_callgraph.compute_logic_calls f t)
    Java_typing.logic_defs_table;

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
      Java_typing.logic_defs_table
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

  Java_options.lprintf "production phase 1.1 : generation of Jessie logic types@.";
  let decls =
(*
    Hashtbl.fold
      (fun _ id acc ->
	 Java_options.lprintf "generating logic type `%s'@." id;
 	 Java_interp.tr_logic_type id acc)
      Java_typing.logic_types_table
*)
      []
  in

  Java_options.lprintf "production phase 1.2 : generation of Jessie range_types@.";
  let decls = Java_interp.range_types decls in

  let non_null_preds, acc, decls_arrays = Java_interp.array_types [] in

  let decls_constants =
    Hashtbl.fold
      (fun _ id acc -> Java_interp.tr_final_static_fields id acc)
      Java_typing.type_table
      [] in

  Java_options.lprintf "production phase 1.4 : generation of Jessie struct types@.";
  let non_null_preds = Java_interp.tr_non_null_logic_fun () :: non_null_preds in
  let decls_java_types, decls_structs =
    Hashtbl.fold
      (fun _ id (acc0, acc) ->
	 Java_interp.tr_class_or_interface id acc0 acc)
      Java_typing.type_table
      ([], decls_arrays)
  in
  let decl_any_string = Java_interp.decl_any_string in
  let decls = decls_structs @ acc @ decls_java_types @ decl_any_string @ decls_constants @ non_null_preds @ decls in


  Java_options.lprintf "production phase 1.3 : generation of Jessie logic functions@.";
  let decls =
    Hashtbl.fold
      (fun _ (li,p) acc ->
	 Java_options.lprintf "generating logic function `%s'@."
	   li.java_logic_info_name;
	 Java_interp.tr_logic_fun li (p :> Java_typing.logic_decl_body) acc)
      Java_typing.logic_defs_table
      decls
  in
  let decls =
    Hashtbl.fold Java_interp.tr_axiomatic Java_typing.axiomatics_table
      decls
  in
  (* production phase 1.5 : generation of Jessie lemmas *)
  let lemmas =
    Hashtbl.fold
      (fun id (loc,lab,p) acc -> (id,Loc.extract loc,lab,p)::acc)
      Java_typing.lemmas_table
      []
  in
  let compare_locs (id1,(_,l1,_,_),_,_) (id2,(_,l2,_,_),_,_) =
    let c = Pervasives.compare l1 l2 in
    if c = 0 then Pervasives.compare id1 id2 else c
  in
  let lemmas = List.sort compare_locs lemmas in
  let decls =
    List.fold_left
      (fun acc (id,loc,lab,p) ->
	 Java_options.lprintf "generating lemma `%s'@."  id;
	 Java_interp.tr_axiom id false loc lab p acc)
      decls
      lemmas
  in

  (* any_string function *)
  (*  let decls = Java_interp.any_string_decl :: decls in *)
  (* class invariants *)
  let decls =
    Hashtbl.fold
      (fun _ (ci, id, invs) acc ->
	 Java_interp.tr_invariants ci id invs acc)
      Java_typing.invariants_table decls
  in

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


  (* production phase 4 : generation of Jessie functions *)
  let decls =
    Array.fold_left
      (fun acc l ->
         let methods,constrs =
	   List.fold_left
	     (fun (m,c) f ->
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
		      (Java_interp.tr_method_spec mi
		        mt.Java_typing.mt_requires
		        mt.Java_typing.mt_decreases
		        mt.Java_typing.mt_behaviors
		        mt.Java_typing.mt_body m, c)
		  | ConstructorInfo ci ->
		      let ct = Hashtbl.find Java_typing.constructors_table
		        ci.constr_info_tag
		      in
		      printf "Generating JC function %s for constructor %s@."
		        ci.constr_info_trans_name
		        ci.constr_info_class.class_info_name;
		      (m,Java_interp.tr_constr_spec ci
		         ct.Java_typing.ct_requires
		         ct.Java_typing.ct_behaviors
                         ct.Java_typing.ct_body c))
             ([],[])
             l
         in
         let acc =
           List.fold_left
             (fun acc m ->
                Java_interp.tr_method_body m acc)
	     acc
             methods
         in
         List.fold_left
           (fun acc c ->
              Java_interp.tr_constr_body c acc)
	   acc
           constrs)
      decls
      components
  in

  (* production phase 5 : produce Jessie file *)
  let decls =
    (mkinvariant_policy_def ~value:!Java_options.inv_sem ())
    :: (mktermination_policy_def ~value:!Java_options.termination_policy ())
    :: (mkseparation_policy_def ~value:!Java_options.separation_policy ())
    :: (mkannotation_policy_def ~value:!Java_options.annotation_sem ())
    :: (mkabstract_domain_def ~value:!Java_options.ai_domain ())
    :: List.rev decls
  in
  let f = List.hd files in
  let f = Filename.chop_extension f in
  let cout = Pp.print_in_file_no_close
    (fun fmt -> fprintf fmt "%a@." Jc_poutput.pdecls decls)
    (f ^ ".jc")
  in
  output_string cout "/*\n";
  output_string cout "Local Variables:\n";
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
  Pp.print_in_file Output.old_print_pos (f ^ ".jloc");

  printf "Done.@.";
  if not !Java_options.gen_only then
    begin
      printf "Calling Jessie...@.";
      let ret = Sys.command ("jessie -why3ml -locs " ^ f ^ ".jloc " ^ f ^ ".jc") in
      if ret <> 0 then
        printf "Jessie failed, abort.@."
      else
        begin
          let d = Filename.dirname f in
          let b = Filename.basename f in
          printf "Calling Why3...@.";
          let _ret = Sys.command ("make -C " ^ d ^" -f " ^ b ^ ".makefile why3ide") in
          ()
        end
    end


(*   with *)
(*     | Java_typing.Typing_error(l,s) -> *)
(* 	eprintf "%a: typing error: %s@." Loc.gen_report_position l s; *)
(* 	exit 1 *)
(*     | Java_options.Java_error(l,s) -> *)
(* 	eprintf "%a: %s@." Loc.gen_report_position l s; *)
(* 	exit 1 *)


let _ =
  Sys.catch_break true;
  Java_typing.catch_typing_errors main ()


(*
  Local Variables:
  compile-command: "LC_ALL=C make -j -C .. bin/krakatoa.byte"
  End:
*)
