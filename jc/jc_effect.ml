(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
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


(* $Id: jc_effect.ml,v 1.62 2007-11-20 14:58:58 marche Exp $ *)


open Jc_env
open Jc_envset
open Jc_fenv
open Jc_ast
open Jc_pervasives
open Jc_iterators
open Format
open Pp


let ef_union ef1 ef2 =
  { jc_effect_alloc_table = 
      StringSet.union
	ef1.jc_effect_alloc_table ef2.jc_effect_alloc_table;
    jc_effect_tag_table = 
      StringSet.union
	ef1.jc_effect_tag_table ef2.jc_effect_tag_table;
    jc_effect_memories = 
      FieldSet.union 
	ef1.jc_effect_memories ef2.jc_effect_memories;
    jc_effect_globals = 
      VarSet.union 
	ef1.jc_effect_globals ef2.jc_effect_globals;
    jc_effect_through_params = 
      VarSet.union 
	ef1.jc_effect_through_params ef2.jc_effect_through_params;
    jc_effect_mutable =
      StringSet.union
	ef1.jc_effect_mutable ef2.jc_effect_mutable;
    jc_effect_committed =
      StringSet.union
	ef1.jc_effect_committed ef2.jc_effect_committed;
  }

let fef_union fef1 fef2 =
  { jc_reads = ef_union fef1.jc_reads fef2.jc_reads ;
    jc_writes = ef_union fef1.jc_writes fef2.jc_writes ;
    jc_raises = ExceptionSet.union fef1.jc_raises fef2.jc_raises;
  }

let add_memory_effect ef fi =
  { ef with jc_effect_memories = FieldSet.add fi ef.jc_effect_memories } 
  
let add_global_effect ef vi =
  { ef with jc_effect_globals = VarSet.add vi ef.jc_effect_globals } 

let add_through_param_effect ef vi =
  { ef with jc_effect_through_params = 
      VarSet.add vi ef.jc_effect_through_params } 
  
let add_alloc_effect ef a =
  { ef with jc_effect_alloc_table = StringSet.add a ef.jc_effect_alloc_table } 
  
let add_tag_effect ef a =
  { ef with jc_effect_tag_table = StringSet.add a ef.jc_effect_tag_table } 

let add_mutable_effect ef st =
  { ef with jc_effect_mutable = StringSet.add st ef.jc_effect_mutable }
  
let add_committed_effect ef st =
  { ef with jc_effect_committed = StringSet.add st ef.jc_effect_committed }

let add_exception_effect ef a =
  { ef with jc_raises = ExceptionSet.add a ef.jc_raises }
  
let add_field_reads fef fi =
  { fef with jc_reads = add_memory_effect fef.jc_reads fi }

let add_global_reads fef vi =
  { fef with jc_reads = add_global_effect fef.jc_reads vi }

let add_through_param_reads fef vi =
  { fef with jc_reads = add_through_param_effect fef.jc_reads vi }

let add_alloc_reads fef a =
  { fef with jc_reads = add_alloc_effect fef.jc_reads a }

let add_tag_reads fef a =
  { fef with jc_reads = add_tag_effect fef.jc_reads a }

let add_mutable_reads fef st =
  { fef with jc_reads = add_mutable_effect fef.jc_reads st }

let add_committed_reads fef st =
  { fef with jc_reads = add_committed_effect fef.jc_reads st }

let add_field_writes fef fi =
  { fef with jc_writes = add_memory_effect fef.jc_writes fi }

let add_global_writes fef vi =
  { fef with jc_writes = add_global_effect fef.jc_writes vi }

let add_through_param_writes fef vi =
  { fef with jc_writes = add_through_param_effect fef.jc_writes vi }

let add_alloc_writes fef a =
  { fef with jc_writes = add_alloc_effect fef.jc_writes a }

let add_tag_writes fef a =
  { fef with jc_writes = add_tag_effect fef.jc_writes a }

let add_mutable_writes fef st =
  { fef with jc_writes = add_mutable_effect fef.jc_writes st }

let add_committed_writes fef st =
  { fef with jc_writes = add_committed_effect fef.jc_writes st }

let same_effects ef1 ef2 =
  StringSet.equal ef1.jc_effect_alloc_table ef2.jc_effect_alloc_table
  && StringSet.equal ef1.jc_effect_tag_table ef2.jc_effect_tag_table
  && FieldSet.equal ef1.jc_effect_memories ef2.jc_effect_memories
  && VarSet.equal ef1.jc_effect_globals ef2.jc_effect_globals
  && VarSet.equal ef1.jc_effect_through_params ef2.jc_effect_through_params
  && StringSet.equal ef1.jc_effect_mutable ef2.jc_effect_mutable
  && StringSet.equal ef1.jc_effect_committed ef2.jc_effect_committed
    
let same_feffects fef1 fef2 =
  same_effects fef1.jc_reads fef2.jc_reads 
  && same_effects fef1.jc_writes fef2.jc_writes 
  && ExceptionSet.equal fef1.jc_raises fef2.jc_raises


(***********************

terms and assertions 

**************************)

let rec term ef t =
  fold_term
    (fun ef t -> match t.jc_term_node with
    | JCTvar vi ->
	if vi.jc_var_info_static then
	  add_global_effect ef vi
	else ef
    | JCToffset(_,t,st) ->
	add_alloc_effect (term ef t) st.jc_struct_info_root
    | JCTapp (li, tl) -> 
	let ef = 
	  List.fold_left2 (fun ef param arg ->
	    if VarSet.mem param 
	      li.jc_logic_info_effects.jc_effect_through_params then
		match (skip_term_shifts arg).jc_term_node with
		  | JCTvar vi ->
		      if vi.jc_var_info_formal then 
			add_through_param_effect ef vi 
		      else ef
		  | _ -> ef
	    else ef
	  ) ef li.jc_logic_info_parameters tl 
	in
	let efli = { 
	  li.jc_logic_info_effects with jc_effect_through_params = VarSet.empty;
	} in
	ef_union efli ef
    | JCTderef (t, fi) ->
	add_memory_effect ef fi
    | _ -> ef
    ) ef t

let tag ef t h =
  let ef = match h with
    | None -> ef
    | Some h -> add_tag_effect ef h
  in
  match t.jc_tag_node with
    | JCTtag _
    | JCTbottom -> ef
    | JCTtypeof(t, _) -> term ef t

let rec assertion ef a =
  match a.jc_assertion_node with
    | JCAtrue | JCAfalse -> ef
    | JCAif (_, _, _) -> assert false (* TODO *)
    | JCAbool_term t -> term ef t
    | JCAinstanceof (t, st) -> 
	add_tag_effect (term ef t) st.jc_struct_info_root
    | JCAnot a
    | JCAold a -> assertion ef a
    | JCAquantifier(_,vi, a) -> assertion ef a 
    | JCArelation (t1,_,t2) -> term (term ef t1) t2
    | JCAapp (li, tl) -> 
	ef_union li.jc_logic_info_effects
	  (List.fold_left term ef tl)	
    | JCAiff (a1, a2)
    | JCAimplies (a1, a2) -> assertion (assertion ef a1) a2
    | JCAand al | JCAor al -> List.fold_left assertion ef al
    | JCAmutable (t, st, ta) ->
	term (add_mutable_effect (tag ef ta (Some st.jc_struct_info_root)) st.jc_struct_info_root) t
    | JCAtagequality (t1, t2, h) ->
	tag (tag ef t1 h) t2 h

(********************

expressions and statements

***********************)

let rec expr ef e =
  match e.jc_expr_node with
    | JCEconst _ -> ef
    | JCEcast(e,st)
    | JCEinstanceof(e,st) -> 
	add_tag_reads (expr ef e) st.jc_struct_info_root
    | JCEderef (e, f) -> 
	let ef = add_field_reads (expr ef e) f in
	begin match (skip_shifts e).jc_expr_node with
	  | JCEvar vi ->
	      if vi.jc_var_info_formal then 
		add_through_param_reads ef vi 
	      else ef
	  | _ -> ef
	end
    | JCEshift (e1, e2)
    | JCEsub_pointer (e1, e2) -> expr (expr ef e1) e2
    | JCEif(e1,e2,e3) -> expr (expr (expr ef e1) e2) e3
    | JCEvar vi -> 
	if vi.jc_var_info_static then
	  add_global_reads ef vi
	else ef
    | JCErange_cast(_,e1)
    | JCEunary(_,e1) -> expr ef e1
    | JCEbinary(e1,op,e2) -> expr (expr ef e1) e2
    | JCEoffset(k,e,st) -> expr ef e
    | JCEalloc(e,st) ->
	let name = st.jc_struct_info_root in
	add_alloc_writes (add_tag_writes ef name) name
(*
	let mut = Jc_invariants.mutable_name st.jc_struct_info_root in
	add_global_writes ef mut
*)
    | JCEfree e ->
	begin match e.jc_expr_type with
	  | JCTpointer(st, _, _) ->
	      let name = st.jc_struct_info_root in
	      (* write tag table ? *)
	      add_alloc_writes (add_tag_writes ef name) name
	  | _ -> assert false
	end

let rec loop_annot ef la = 
  let ef = assertion ef la.jc_loop_invariant in
  match la.jc_loop_variant with
  | None -> ef
  | Some t -> term ef t

let rec statement ef s =
  match s.jc_statement_node with
    | JCSreturn_void -> ef
    | JCScall (_, fi, le, s) -> 
	let through_param ef = 
	  List.fold_left2 (fun ef param arg ->
	    if VarSet.mem param ef.jc_effect_through_params then
	      match (skip_shifts arg).jc_expr_node with
		| JCEvar vi ->
		    if vi.jc_var_info_formal then 
		      add_through_param_effect ef vi 
		    else ef
		| _ -> ef
	    else ef
	  ) empty_effects fi.jc_fun_info_parameters le
	in
	let effi = { 
	  fi.jc_fun_info_effects with
	    jc_reads = through_param fi.jc_fun_info_effects.jc_reads;
	    jc_writes = through_param fi.jc_fun_info_effects.jc_writes;
	} in
	let ef = fef_union effi (List.fold_left expr ef le) in
	statement ef s
    | JCSassign_heap (e1, fi, e2) ->
	let ef = expr (expr (add_field_writes ef fi) e1) e2 in
	begin match (skip_shifts e1).jc_expr_node with
	  | JCEvar vi ->
	      if vi.jc_var_info_formal then 
		add_through_param_writes ef vi 
	      else ef	
	  | _ -> ef
	end
    | JCSassign_var (vi, e) ->
	if vi.jc_var_info_static then
	  add_global_writes (expr ef e) vi
	else 
	  expr ef e
    | JCSreturn(_,e) -> expr ef e
    | JCSpack(st, e, _) ->
	let ef = expr ef e in
	(* Assert the invariants of the structure => need the reads of the invariants *)
	let (_, invs) = Hashtbl.find Jc_typing.structs_table st.jc_struct_info_name in
	let ef =
	  List.fold_left
	    (fun ef (li, _) -> { ef with jc_reads = ef_union ef.jc_reads li.jc_logic_info_effects })
	    ef
	    invs
	in
	(* Fields *)
	let ef = List.fold_left
	  (fun ef fi ->
	     match fi.jc_field_info_type with
	       | JCTpointer(st, _, _) ->
	           (* Assert fields fully mutable => need mutable and tag_table (of field) as reads *)
		   let ef = add_mutable_reads ef st.jc_struct_info_root in
		   let ef = add_tag_reads ef st.jc_struct_info_root in
	           (* Modify field's "committed" field => need committed (of field) as reads and writes *)
		   let ef = add_committed_reads ef st.jc_struct_info_root in
		   let ef = add_committed_writes ef st.jc_struct_info_root in
		   (* ...and field as reads *)
		   add_field_reads ef fi
	       | _ -> ef)
	  ef
	  st.jc_struct_info_fields in
	(* Change structure mutable => need mutable as reads and writes *)
	let ef = add_mutable_reads ef st.jc_struct_info_root in
	let ef = add_mutable_writes ef st.jc_struct_info_root in
        (* And that's all *)
	ef
    | JCSunpack(st, e, _) ->
	let ef = expr ef e in
	(* Change structure mutable => need mutable as reads and writes *)
	let ef = add_mutable_reads ef st.jc_struct_info_root in
	let ef = add_mutable_writes ef st.jc_struct_info_root in
	(* Fields *)
	let ef = List.fold_left
	  (fun ef fi ->
	     match fi.jc_field_info_type with
	       | JCTpointer(st, _, _) ->
	           (* Modify field's "committed" field => need committed (of field) as reads and writes *)
		   let ef = add_committed_reads ef st.jc_struct_info_root in
		   let ef = add_committed_writes ef st.jc_struct_info_root in
		   (* ...and field as reads *)
		   add_field_reads ef fi
	       | _ -> ef)
	  ef
	  st.jc_struct_info_fields in
	(* And that's all *)
	ef
    | JCSthrow (ei, Some e) -> 
	add_exception_effect (expr ef e) ei
    | JCSthrow (ei, None) -> 
	add_exception_effect ef ei
    | JCStry (s, catches, finally) -> 
	let ef = 
	  List.fold_left 
	    (fun ef (excep,_,s) -> 
	       let ef = 
		 { ef with 
		     jc_raises = ExceptionSet.remove excep ef.jc_raises }
	       in
	       statement ef s)
	    (statement ef s) catches
	in
	statement ef finally
    | JCSloop (la, s) -> 
	let ef = {ef with jc_reads = loop_annot ef.jc_reads la } in
	statement ef s
    | JCSif (e, s1, s2) -> 
	statement (statement (expr ef e) s1) s2
    | JCSdecl(vi,e,s) -> 
	statement (Option_misc.fold_left expr ef e) s
    | JCSassert((*_,*)a) -> ef
    | JCSblock l -> List.fold_left statement ef l

(* Conservatively consider location is both read and written. *)
let location ef l =
  match l with
    | JCLderef(t,fi) ->
	let ef = add_field_writes ef fi in
	let ef = add_field_reads ef fi in
	begin match skip_tloc_range t with
	  | JCLSvar vi ->
	      if vi.jc_var_info_formal then 
		add_through_param_reads ef vi 
	      else ef
	  | _ -> ef
	end
    | JCLvar vi ->
	if vi.jc_var_info_static then
	  begin
	    let ef = add_global_writes ef vi in
	    add_global_reads ef vi
	  end
	else ef

let behavior ef (_, b) =
  (* assigns *)
  let ef = Option_misc.fold
    (fun x ef -> List.fold_left location ef x) 
    b.jc_behavior_assigns ef
  in
    (* requires: reads *)
    (*
      let ef = match b.jc_behavior_requires with
      None -> ef
      | Some r ->	{ ef with jc_reads = assertion ef.jc_reads r }
      in
    *)
    (* assumes: reads *)
  let ef = match b.jc_behavior_assumes with
      None -> ef
    | Some a ->	{ ef with jc_reads = assertion ef.jc_reads a }
  in
    (* ensures: reads *)
  let ef = 
    { ef with jc_reads = assertion ef.jc_reads b.jc_behavior_ensures } 
  in
    (* throws: raises *)
    Option_misc.fold_left add_exception_effect ef b.jc_behavior_throws

let spec ef s = 
  let ef = List.fold_left behavior ef s.jc_fun_behavior in
  { ef with jc_reads = assertion ef.jc_reads s.jc_fun_requires }

let parameter ef vi =
  match vi.jc_var_info_type with
    | JCTpointer(st, _, _) ->
	let name = st.jc_struct_info_root in
	add_alloc_reads (add_tag_reads ef name) name
    | _ -> ef

(* computing the fixpoint *)

let fixpoint_reached = ref false

let logic_fun_effects f = 
  let (f,ta) = 
    Hashtbl.find Jc_typing.logic_functions_table f.jc_logic_info_tag 
  in
  let ef = f.jc_logic_info_effects in
  let ef = match ta with
    | JCTerm t -> term ef t
    | JCAssertion a -> assertion ef a
    | JCReads r ->
	List.fold_left
	  (fun ef l ->
	     let ef = {
	       jc_reads = ef;
	       jc_writes = ef; (* could be anything *)
	       jc_raises = ExceptionSet.empty;
	     }
	     in (location ef l).jc_reads)
	  ef r
  in
  if same_effects ef f.jc_logic_info_effects then ()
  else begin
    fixpoint_reached := false;
    f.jc_logic_info_effects <- ef
  end

let fun_effects fi =
  let (f, s, b) = 
    Hashtbl.find Jc_norm.functions_table fi.jc_fun_info_tag 
  in
  let ef = f.jc_fun_info_effects in
  let ef = spec ef s in
  let ef = Option_misc.fold_left (List.fold_left statement) ef b in
  let ef = List.fold_left parameter ef f.jc_fun_info_parameters in
  if same_feffects ef f.jc_fun_info_effects then ()
  else begin
    fixpoint_reached := false;
    f.jc_fun_info_effects <- ef
  end
    
  let logic_effects funs =
  fixpoint_reached := false;
  while not !fixpoint_reached do
    fixpoint_reached := true;
    Jc_options.lprintf "Effects: doing one iteration...@.";
    List.iter logic_fun_effects funs
  done;
  Jc_options.lprintf "Effects: fixpoint reached@.";
  List.iter
    (fun f ->
       Jc_options.lprintf
	 "Effects for logic function %s:@\n@[ reads alloc_table: %a@]@\n@[ reads tag_table: %a@]@\n@[ reads memories: %a@]@." 
	 f.jc_logic_info_name
	 (print_list comma (fun fmt v -> fprintf fmt "%s" v))
	 (StringSet.elements f.jc_logic_info_effects.jc_effect_alloc_table)
	 (print_list comma (fun fmt v -> fprintf fmt "%s" v))
	 (StringSet.elements f.jc_logic_info_effects.jc_effect_tag_table)
	 (print_list comma (fun fmt field ->
			     fprintf fmt "%s" field.jc_field_info_name))
	 (FieldSet.elements f.jc_logic_info_effects.jc_effect_memories))
    funs

let function_effects funs =
  fixpoint_reached := false;
  while not !fixpoint_reached do
    fixpoint_reached := true;
    Jc_options.lprintf "Effects: doing one iteration...@.";
    List.iter fun_effects funs
  done;
  Jc_options.lprintf "Effects: fixpoint reached@.";
  Jc_options.lprintf "Effects: removing global reads without writes@.";
  List.iter 
    (fun f ->
       f.jc_fun_info_effects <-
	 let efw = f.jc_fun_info_effects.jc_writes.jc_effect_globals in
	 let efr = f.jc_fun_info_effects.jc_reads.jc_effect_globals in
	 let efg = VarSet.inter efr efw in
	 let ef = { f.jc_fun_info_effects.jc_reads 
		    with jc_effect_globals = efg } in
	   { f.jc_fun_info_effects with jc_reads = ef }
    ) funs;
  List.iter
    (fun f ->
       Jc_options.lprintf
	 "Effects for function %s:@\n@[ reads: %a@]@\n@[ writes: %a@]@\n@[ raises: %a@]@." 
	 f.jc_fun_info_name
	 (print_list comma
	    (fun fmt field -> fprintf fmt "%s" field.jc_field_info_name))
	 (FieldSet.elements f.jc_fun_info_effects.jc_reads.jc_effect_memories)
	 (print_list comma
	    (fun fmt field -> fprintf fmt "%s" field.jc_field_info_name))
	 (FieldSet.elements f.jc_fun_info_effects.jc_writes.jc_effect_memories)
	 (print_list comma 
	    (fun fmt ei -> fprintf fmt "%s" ei.jc_exception_info_name))
	 (ExceptionSet.elements f.jc_fun_info_effects.jc_raises))
    funs


(*
  Local Variables: 
  compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
  End: 
*)
