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

(* $Id: jc_separation.ml,v 1.2 2007-12-17 13:18:48 moy Exp $ *)

open Jc_env
open Jc_envset
open Jc_fenv
open Jc_ast
open Format
open Jc_iterators
open Jc_region
open Jc_pervasives
open Pp

let expr e = 
  iter_expr (fun e -> match e.jc_expr_node with
    | JCEsub_pointer(e1,e2) | JCEif(_,e1,e2) ->
	Region.unify e1.jc_expr_region e2.jc_expr_region
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
	let regions = f.jc_fun_info_regions in
	let assoc = Region.copy_list regions in
	call.jc_call_region_assoc <- assoc;
	let param_regions =
	  List.map (fun vi -> 
	    if is_dummy_region vi.jc_var_info_region then dummy_region else
	      try Region.assoc vi.jc_var_info_region assoc
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
	      try Region.assoc f.jc_fun_info_return_region assoc
	      with Not_found -> assert false
	  in
	  Jc_options.lprintf "param:%a@." Region.print result_region;
	  Jc_options.lprintf "arg:%a@." Region.print vi.jc_var_info_region;
	  Region.unify result_region vi.jc_var_info_region
	end
    | JCSreturn(ty,e) ->
	Region.unify rresult e.jc_expr_region
    | JCSdecl _ | JCSblock _ | JCSif _ | JCStry _ | JCSloop _
    | JCSassert _ | JCSreturn_void | JCSpack _ | JCSunpack _ -> 
	()
  ) s

let code_function fi =
  let (f, _, s, b) = 
    Hashtbl.find Jc_norm.functions_table fi.jc_fun_info_tag 
  in
  Jc_options.lprintf "Separation: treating function %s@." f.jc_fun_info_name;
  Option_misc.iter (List.iter (statement fi.jc_fun_info_return_region)) b;
  let param_regions =
    List.map (fun vi -> vi.jc_var_info_region) f.jc_fun_info_parameters in
  let fun_regions = fi.jc_fun_info_return_region :: param_regions in
  let fun_regions = List.filter (fun r -> not(is_dummy_region r)) fun_regions in
  fi.jc_fun_info_regions <- Region.reachable_list fun_regions

let code_component fil =
  List.iter code_function fil


(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
