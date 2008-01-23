(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
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

(* $Id: jc_separation.ml,v 1.12 2008-01-23 15:18:12 bardou Exp $ *)

open Jc_env
open Jc_envset
open Jc_fenv
open Jc_ast
open Format
open Jc_iterators
open Jc_region
open Jc_pervasives
open Pp

let term rresult t =
  iter_term (fun t -> match t.jc_term_node with
    | JCTvar vi ->	
	if vi.jc_var_info_name = "\\result" then 
	  Region.unify rresult vi.jc_var_info_region
    | JCTsub_pointer(t1,t2) | JCTif(_,t1,t2) ->
	Region.unify t1.jc_term_region t2.jc_term_region
    | JCTmatch(_, (_, t1)::rem) ->
	List.iter
	  (fun (_, t2) -> Region.unify t1.jc_term_region t2.jc_term_region)
	  rem
    | JCTmatch(_, []) ->
	()
    | JCTapp app ->
	let li = app.jc_app_fun in
	let regions = li.jc_logic_info_param_regions in
	let assoc = RegionList.duplicate regions in
	app.jc_app_region_assoc <- assoc;
	let param_regions =
	  List.map (fun vi -> 
	    if is_dummy_region vi.jc_var_info_region then dummy_region else
	      try RegionList.assoc vi.jc_var_info_region assoc
	      with Not_found -> assert false)
	    li.jc_logic_info_parameters
	in
	let arg_regions = 
	  List.map (fun t -> t.jc_term_region) app.jc_app_args
	in
	Jc_options.lprintf "param:%a@." (print_list comma Region.print) param_regions;
	Jc_options.lprintf "arg:%a@." (print_list comma Region.print) arg_regions;
	List.iter2 Region.unify param_regions arg_regions;
	let result_region = 
	  try RegionList.assoc li.jc_logic_info_result_region assoc
	  with Not_found -> assert false
	in
	Jc_options.lprintf "param:%a@." Region.print result_region;
	Jc_options.lprintf "arg:%a@." Region.print t.jc_term_region;
	Region.unify result_region t.jc_term_region
    | JCTconst _ | JCTrange(None,None) | JCTbinary _ | JCTshift _
    | JCTrange _ | JCTunary _ | JCTderef _ | JCTold _ | JCTat _ | JCToffset _
    | JCTinstanceof _ | JCTcast _ ->
	()
  ) t

let assertion rresult a =
  iter_term_and_assertion (term rresult) 
    (fun a -> match a.jc_assertion_node with
      | JCAapp _ -> () (* TODO *)
      | JCAtrue | JCAfalse | JCArelation _  | JCAtagequality _ 
      | JCAinstanceof _ | JCAbool_term _ | JCAmutable _ 
      | JCAand _ | JCAor _ | JCAimplies _ | JCAiff _ | JCAif _ (*| JCAmatch _*)
      | JCAnot _ | JCAquantifier _ | JCAold _ | JCAat _ ->
	  ()
    ) a

let expr e = 
  iter_expr (fun e -> match e.jc_expr_node with
    | JCEsub_pointer(e1,e2) | JCEif(_,e1,e2) ->
	Region.unify e1.jc_expr_region e2.jc_expr_region
(*    | JCEmatch(_, (_, e1)::rem) ->
	List.iter
	  (fun (_, e2) -> Region.unify e1.jc_expr_region e2.jc_expr_region)
	  rem
    | JCEmatch(_, []) ->
	()*)
    | JCEconst _ | JCEvar _ | JCEbinary _ | JCEshift _ | JCEunary _
    | JCEderef _ | JCEoffset _ | JCEinstanceof _ | JCEcast _ 
    | JCErange_cast _ | JCEalloc _ | JCEfree _ ->
	()
  ) e

let statement rresult s =
  iter_expr_and_statement expr (fun s -> match s.jc_statement_node with
    | JCSdecl(vi,Some e,_) | JCSassign_var(vi,e) ->
	Region.unify vi.jc_var_info_region e.jc_expr_region
    | JCSassign_heap(e1,fi,e2) ->
	let fr = Region.make_field e1.jc_expr_region fi in
	Region.unify fr e2.jc_expr_region
    | JCSthrow(ei,_) ->
	begin match ei.jc_exception_info_type with None -> () | Some ty ->
	  assert(not(is_pointer_type ty)) (* TODO *)
	end
    | JCScall(vio,call,s) -> 
	let f = call.jc_call_fun in
	let regions = f.jc_fun_info_param_regions in
	let assoc = RegionList.duplicate regions in
	call.jc_call_region_assoc <- assoc;
	let param_regions =
	  List.map (fun vi -> 
	    if is_dummy_region vi.jc_var_info_region then dummy_region else
	      try RegionList.assoc vi.jc_var_info_region assoc
	      with Not_found -> assert false)
	    f.jc_fun_info_parameters
	in
	let arg_regions = 
	  List.map (fun e -> e.jc_expr_region) call.jc_call_args
	in
	Jc_options.lprintf "param:%a@." (print_list comma Region.print) param_regions;
	Jc_options.lprintf "arg:%a@." (print_list comma Region.print) arg_regions;
	List.iter2 Region.unify param_regions arg_regions;
	begin match vio with None -> () | Some vi ->
	  let result_region = 
	    if is_dummy_region f.jc_fun_info_return_region then dummy_region
	    else
	      try RegionList.assoc f.jc_fun_info_return_region assoc
	      with Not_found -> assert false
	  in
	  Jc_options.lprintf "param:%a@." Region.print result_region;
	  Jc_options.lprintf "arg:%a@." Region.print vi.jc_var_info_region;
	  Region.unify result_region vi.jc_var_info_region
	end
    | JCSreturn(ty,e) ->
	Region.unify rresult e.jc_expr_region
    | JCSlabel(lab,s) -> ()
    | JCSassert a ->
	assertion rresult a
    | JCSloop(la,_) ->
	iter_term_and_assertion_in_loop_annot 
	  (term rresult) (assertion rresult) la
    | JCSdecl _ | JCSblock _ | JCSif _ | JCSmatch _ | JCStry _ 
    | JCSreturn_void | JCSpack _ | JCSunpack _ -> 
	()
  ) s

let logic_function f =
  let (f, ta) = 
    Hashtbl.find Jc_typing.logic_functions_table f.jc_logic_info_tag 
  in
  let rresult = f.jc_logic_info_result_region in
  begin match ta with
    | JCTerm t -> term rresult t
    | JCAssertion a -> assertion rresult a
    | JCReads r -> () (* TODO *)
  end;
  let param_regions =
    List.map (fun vi -> vi.jc_var_info_region) f.jc_logic_info_parameters in
  let fun_regions = f.jc_logic_info_result_region :: param_regions in
  f.jc_logic_info_param_regions <- RegionList.reachable fun_regions

let logic_component fls =
  List.iter logic_function fls

let code_function f =
  let (f, _, spec, body) = 
    Hashtbl.find Jc_norm.functions_table f.jc_fun_info_tag 
  in
  Jc_options.lprintf "Separation: treating function %s@." f.jc_fun_info_name;
  let rresult = f.jc_fun_info_return_region in
  iter_term_and_assertion_in_fun_spec (term rresult) (assertion rresult) spec;
  Option_misc.iter (List.iter (statement rresult)) body;
  let param_regions =
    List.map (fun vi -> vi.jc_var_info_region) f.jc_fun_info_parameters in
  let fun_regions = f.jc_fun_info_return_region :: param_regions in
  f.jc_fun_info_param_regions <- RegionList.reachable fun_regions

let code_component fls =
  List.iter code_function fls

let axiom id (labels,a) = assertion (* labels *) dummy_region a

let regionalize_assertion a assoc =
  map_term_in_assertion (fun t ->
    let t = match t.jc_term_node with
      | JCTapp app ->
	  let app_assoc = 
	    List.map (fun (rdist,rloc) -> 
	      try (rdist,RegionList.assoc rloc assoc) with Not_found -> (rdist,rloc)
	    ) app.jc_app_region_assoc
	  in
	  let tnode = JCTapp { app with jc_app_region_assoc = app_assoc; } in
	  { t with jc_term_node = tnode; }
      | JCTconst _ | JCTvar _ | JCTshift _ | JCTsub_pointer _ 
      | JCTderef _ | JCTbinary _ | JCTunary _ | JCTold _ | JCTat _ | JCToffset _
      | JCTinstanceof _ | JCTcast _ | JCTif _ | JCTmatch _ | JCTrange _ ->
	  t
    in
    try { t with jc_term_region = RegionList.assoc t.jc_term_region assoc; }
    with Not_found -> t
  ) a
  
(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
