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


(* $Id: jc_effect.ml,v 1.12 2006-11-27 08:40:00 marche Exp $ *)


open Jc_env
open Jc_envset
open Jc_fenv
open Jc_ast

let ef_union ef1 ef2 =
  { jc_effect_alloc_table = 
      VarSet.union
	ef1.jc_effect_alloc_table ef2.jc_effect_alloc_table;
    jc_effect_memories = 
      FieldSet.union 
	ef1.jc_effect_memories ef2.jc_effect_memories }

let fef_union fef1 fef2 =
  { jc_reads = ef_union fef1.jc_reads fef2.jc_reads ;
    jc_writes = ef_union fef1.jc_writes fef2.jc_writes }

let add_memory_effect ef fi =
  { ef with jc_effect_memories = FieldSet.add fi ef.jc_effect_memories } 
  
let add_field_reads fef fi =
  { fef with jc_reads = add_memory_effect fef.jc_reads fi }

let add_field_writes fef fi =
  { fef with jc_writes = add_memory_effect fef.jc_writes fi }
 
let same_effects ef1 ef2 =
  VarSet.equal ef1.jc_effect_alloc_table ef2.jc_effect_alloc_table &&
  FieldSet.equal ef1.jc_effect_memories ef2.jc_effect_memories

let same_feffects fef1 fef2 =
  same_effects fef1.jc_reads fef2.jc_reads &&
  same_effects fef1.jc_writes fef2.jc_writes

(***********************

terms and assertions 

**************************)

let rec term ef t =
  match t.jc_term_node with
    | JCTconst _ -> ef
    | JCTvar vi -> ef (* TODO ? *)
    | JCTif(t1, t2, t3) -> term (term (term ef t1) t2) t3
    | JCTcast(t, _) 
    | JCTinstanceof (t, _)
    | JCToffset_min t 
    | JCToffset_max t
    | JCTold t -> term ef t
    | JCTapp (li, tl) -> 
	ef_union li.jc_logic_info_effects
	  (List.fold_left term ef tl)	
    | JCTderef (t, fi) ->
	term (add_memory_effect ef fi) t
    | JCTshift (t1, t2) -> term (term ef t1) t2

let rec assertion ef a =
  match a.jc_assertion_node with
    | JCAtrue | JCAfalse -> ef
    | JCAif (_, _, _) -> assert false (* TODO *)
    | JCAbool_term t
    | JCAinstanceof (t, _) -> term ef t
    | JCAnot a
    | JCAold a -> assertion ef a
    | JCAforall (_, _) -> assert false (* TODO *)
    | JCAapp (li, tl) -> 
	ef_union li.jc_logic_info_effects
	  (List.fold_left term ef tl)	
    | JCAiff (a1, a2)
    | JCAimplies (a1, a2) -> assertion (assertion ef a1) a2
    | JCAand al -> List.fold_left assertion ef al

(********************

expressions and statements

***********************)

let rec expr ef e =
  match e.jc_expr_node with
    | JCEconst _ -> ef
    | JCEassign_heap (e1, fi, e2) 
    | JCEassign_op_heap(e1,fi,_,e2) ->
	expr (expr (add_field_writes ef fi) e1) e2
    | JCEassign_op_local (_, _, _) -> assert false
    | JCEassign_local (vi, e) -> expr ef e
    | JCEincr_local(op,vi) -> ef
    | JCEincr_heap _ -> assert false
    | JCEcall (fi, le) -> 
	fef_union fi.jc_fun_info_effects
	  (List.fold_left expr ef le)
    | JCEcast(e,_)
    | JCEinstanceof(e,_) -> expr ef e
    | JCEderef (e, f) -> expr ef e (* TODO *)
    | JCEshift (_, _) -> assert false
    | JCEif(e1,e2,e3) -> expr (expr (expr ef e1) e2) e3
    | JCEvar _ -> ef (* TODO *)

let rec loop_annot ef la = ef 
(*
  assertion (term ef la.jc_loop_variant) la.jc_loop_invariant
*)

let rec statement ef s =
  match s.jc_statement_node with
    | JCSreturn e 
    | JCSpack(_,e) | JCSunpack(_,e)
    | JCSexpr e -> expr ef e
    | JCSthrow (_, _) -> assert false
    | JCStry (_, _, _) -> assert false
    | JCSgoto _ -> assert false
    | JCScontinue _ -> assert false
    | JCSbreak _ -> assert false
    | JCSwhile (c, la, s) -> 
	statement (loop_annot (expr ef c) la) s
    | JCSif (e, s1, s2) -> 
	statement (statement (expr ef e) s1) s2
    | JCSdecl(vi,e,s) -> 
	statement (Option_misc.fold_left expr ef e) s
    | JCSassert _ -> assert false
    | JCSblock l -> List.fold_left statement ef l


let location ef l =
  match l with
    | JCLderef(t,fi) ->
	add_field_writes ef fi
    | JCLvar _ -> assert false (* TODO *)

let behavior ef (_,b) =
  Option_misc.fold 
    (fun x ef -> List.fold_left location ef x) 
    b.jc_behavior_assigns ef

let spec ef s = 
  List.fold_left behavior ef s.jc_fun_behavior

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
  in
  if same_effects ef f.jc_logic_info_effects then ()
  else begin
    fixpoint_reached := false;
    f.jc_logic_info_effects <- ef
  end

let fun_effects fi =
  let (f,s,b) = 
    Hashtbl.find Jc_typing.functions_table fi.jc_fun_info_tag 
  in
  let ef = f.jc_fun_info_effects in
  let ef = spec ef s in
  let ef = List.fold_left statement ef b in
  if same_feffects ef f.jc_fun_info_effects then ()
  else begin
    fixpoint_reached := false;
    f.jc_fun_info_effects <- ef
  end
    
  
open Format
open Pp


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
	 "Effects for logic function %s:\n reads: %a@." f.jc_logic_info_name
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
  List.iter
    (fun f ->
       Jc_options.lprintf
	 "Effects for function %s:\n reads: %a\n writes: %a@." 
	 f.jc_fun_info_name
	 (print_list comma (fun fmt field ->
			     fprintf fmt "%s" field.jc_field_info_name))
	 (FieldSet.elements f.jc_fun_info_effects.jc_reads.jc_effect_memories)
	 (print_list comma (fun fmt field ->
			      fprintf fmt "%s" field.jc_field_info_name))
	 (FieldSet.elements f.jc_fun_info_effects.jc_writes.jc_effect_memories))
    funs

       

  


(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
