(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2015                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
(*                                                                        *)
(*  Jessie2 fork:                                                         *)
(*    Mikhail MANDRYKIN, ISP RAS       (adaptation for Linux sources)     *)
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

open Stdlib
open Env
open Envset
open Region
open Ast
open Fenv

open Constructors
open Common

open Format
open Why_pp

let in_logic_component f = List.exists (Logic_info.equal f)

let in_code_component f = List.exists (Fun_info.equal f)

let call_regions ~pos app in_current_comp param_regions result_region params =
  let arg_regions =
    List.map
      (fun x -> x#region) @@
      match app with
      | `App app -> (app.app_args :> regioned list)
      | `Call call -> (call.call_args :> regioned list)
  in
  if in_current_comp then
    (* No generalization here, plain unification *)
    result_region, List.map (fun vi -> vi.vi_region) params, arg_regions
  else
    (* Apply generalization before unification *)
    let assoc = RegionList.duplicate param_regions in
    begin match app with
    | `App  app  -> app.app_region_assoc <- assoc
    | `Call call -> call.call_region_assoc <- assoc
    end;
    let assoc r =
      try
        if not (is_dummy_region r) then RegionList.assoc r assoc
                                   else dummy_region
      with
      | Not_found ->
        Options.jc_error
          pos
          ("Can't associate generalized region to a local one: %s (%s) in call to %s.\n" ^^
           "Unable to complete region analysis, aborting. Consider using #pragma SeparationPolicy(none)")
          r.r_name r.r_final_name
          (match app with
           | `App { app_fun = { li_name = n } }
           | `Call { call_fun = JClogic_fun { li_name = n } | JCfun { fun_name = n } } -> n)
    in
    let param_regions = List.map (fun vi -> assoc vi.vi_region) params in
    assoc result_region, param_regions, arg_regions

let single_term comp result_region t =
  match t#node with
  | JCTvar { vi_name = "\\result"; vi_region = r } ->
    Region.unify result_region r
  | JCTvar _ -> ()
  | JCTbinary (t1, (_, `Pointer), t2) | JCTif (_, t1, t2) ->
    Region.unify t1#region t2#region
  | JCTmatch (_, (_, t1) :: rem) ->
    List.iter (fun (_, t2) -> Region.unify t1#region t2#region) rem
  | JCTmatch (_, []) -> ()
  | JCTlet (vi, t, _) -> Region.unify vi.vi_region t#region
  | JCTapp app ->
    let li = app.app_fun in
    let result_region, param_regions, arg_regions =
      call_regions
        ~pos:t#pos
        (`App app)
        (in_logic_component li comp)
        li.li_param_regions
        li.li_result_region
        li.li_parameters
    in
    List.iter2 Region.unify param_regions arg_regions;
    Region.unify result_region t#region
  | JCTconst _ | JCTrange (None, None) | JCTbinary _     | JCTshift _
  | JCTrange _ | JCTunary _            | JCTderef _      | JCTold _
  | JCTat _    | JCToffset _           | JCTbase_block _
  | JCTaddress _                       | JCTinstanceof _
  | JCTdowncast _                      | JCTsidecast _
  | JCTrange_cast _                    | JCTrange_cast_mod _
  | JCTreal_cast _ ->
    ()

let term comp result_region = Iterators.iter_term (single_term comp result_region)

let single_assertion comp a =
  match a#node with
  | JCArelation (t1, (_, `Pointer), t2) ->
    begin match t1#node, t2#node with
    | JCTbase_block _, JCTbase_block _ -> ()
    | _ -> Region.unify t1#region t2#region
    end
  | JCArelation _ -> ()
  | JCAapp app ->
    let li = app.app_fun in
    let _, param_regions, arg_regions =
      call_regions
        ~pos:a#pos
        (`App app)
        (in_logic_component li comp)
        li.li_param_regions
        dummy_region
        li.li_parameters
    in
    List.iter2 Region.unify param_regions arg_regions
  | JCAlet (vi, t, _) ->
    Region.unify vi.vi_region t#region
  | JCAtrue         | JCAfalse       | JCAeqtype _
  | JCAinstanceof _ | JCAbool_term _ | JCAmutable _ | JCAfresh _ | JCAallocable _ | JCAfreeable _
  | JCAand _        | JCAor _        | JCAimplies _ | JCAiff _   | JCAif _
  | JCAmatch _      | JCAnot _       | JCAquantifier _
  | JCAold _        | JCAat _        | JCAsubtype _ ->
    ()

let assertion comp result_region =
  Iterators.iter_term_and_assertion (single_term comp result_region) (single_assertion comp)

let single_location = ignore

let single_location_set = ignore

let location comp result_region =
  Iterators.iter_location (single_term comp result_region) single_location single_location_set

let single_expr code_comp logic_comp result_region e =
  match e#node with
  | JCEbinary (e1, _, e2) | JCEif (_, e1, e2) ->
    Region.unify e1#region e2#region
  | JCEmatch (_, (_, e1) :: rem) ->
    List.iter (fun (_, e2) -> Region.unify e1#region e2#region) rem
  | JCEmatch (_, []) -> ()
  | JCElet (vi, Some e, _)
  | JCEassign_var (vi, e) ->
    Region.unify vi.vi_region e#region
  | JCEassign_heap (e1, fi, e2) ->
    let fr = Region.make_field e1#region fi in
    Region.unify fr e2#region
  | JCEthrow (exi, _) ->
    begin match exi.exi_type with
    | Some ty when is_pointer_type ty ->
      Options.jc_error
        e#pos
        "Unsupported pointer in throw clause (TODO)" (* TODO *)
    | Some _ | None -> ()
    end
  | JCEapp call ->
    let in_current_comp, param_regions, result_region, params =
      match call.call_fun with
      | JClogic_fun f ->
        false,                         f.li_param_regions,  f.li_result_region,  f.li_parameters
      | JCfun f ->
        in_code_component f code_comp, f.fun_param_regions, f.fun_return_region, List.map snd f.fun_parameters
    in
    let result_region, param_regions, arg_regions =
      call_regions
        ~pos:e#pos
        (`Call call)
        in_current_comp
        param_regions
        result_region
        params
    in
    List.iter2 Region.unify param_regions arg_regions;
    if e#typ <> unit_type then Region.unify result_region e#region
    (* Otherwise, the result of the call is discarded *)
  | JCEreturn (_ty, e) ->
    Region.unify result_region e#region
  | JCEassert (_behav, _asrt, a) ->
    assertion logic_comp result_region a
  | JCEcontract (req, None, _vi_result, _behs, _e) ->
    (* TODO: decreases, behaviors, etc. *)
    Option.iter (assertion logic_comp result_region) req
  | JCEcontract _ ->
    Options.jc_error
      e#pos
      "Unsupported decreases clause in statement contract"
  | JCEconst _        | JCEvar _        | JCEshift _   | JCEunary _
  | JCEderef _        | JCEoffset _     | JCEaddress _ | JCEinstanceof _
  | JCEdowncast _     | JCEsidecast _   | JCEreinterpret _
  | JCEbase_block _   | JCEfresh _
  | JCErange_cast _   | JCErange_cast_mod _            | JCEreal_cast _
  | JCEalloc _        | JCEfree _
  | JCElet (_, None, _)
  | JCEloop (_, _)    | JCEblock _      | JCEtry _
  | JCEreturn_void    | JCEpack _       | JCEunpack _ ->
    ()

let expr code_comp logic_comp result_region =
  Iterators.iter_expr_and_term_and_assertion
    (single_term logic_comp result_region)
    (single_assertion logic_comp)
    single_location
    single_location_set
    (single_expr code_comp logic_comp result_region)

let axiomatic_decl logic_comp d =
  match d with
  | Typing.ADprop (_, _, _, _, a) ->
    assertion logic_comp dummy_region a

let axiomatic comp a =
  try
    let l = StringHashtblIter.find Typing.axiomatics_table a in
    List.iter (axiomatic_decl comp) l.Typing.axiomatics_decls
  with
  | Not_found ->
    Options.jc_error
      Why_loc.dummy_position
      "separation: axiomatic: can't find axiomatic: %s" a

let logic_function comp f =
  let f, ta = IntHashtblIter.find Typing.logic_functions_table f.li_tag in
  let result_region = f.li_result_region in
  begin match ta with
  | JCNone -> ()
  | JCTerm t ->
    term comp result_region t;
    Region.unify result_region t#region
  | JCAssertion a ->
    assertion comp result_region a
  | JCReads r ->
    List.iter (location comp result_region) r
  | JCInductive l ->
    List.iter (fun (_, _, a) -> assertion comp result_region a) l
  end;
  if ta = JCNone then Option.iter (axiomatic comp) f.li_axiomatic

let logic_component comp =
  let generalize_logic_function f =
    let param_regions = List.map (fun vi -> vi.vi_region) f.li_parameters in
    let fun_regions = f.li_result_region :: param_regions in
    f.li_param_regions <- RegionList.reachable fun_regions
  in
  (* Perform plain unification on component *)
  List.iter (logic_function comp) comp;
  (* Generalize regions accessed *)
  List.iter generalize_logic_function comp;
  (* Fill in association table at each call site *)
  List.iter (logic_function []) comp

let funspec comp result_region spec =
  let unify_logic_apps_in_funspec =
    let single_term acc t =
      let eq_apps app1 app2 =
        app1.app_fun.li_tag = app2.app_fun.li_tag &&
        app1.app_label_assoc = app2.app_label_assoc &&
        List.for_all2 (TermOrd.equal) app1.app_args app2.app_args
      in
      match t#node with
      | JCTapp app ->
        begin match List.mem_assoc_eq eq_apps app acc with
        | None -> (app, t#region) :: acc
        | Some r -> Region.unify r t#region; acc
        end
      | _ -> acc
    in
    let dummy acc _ = acc in
    ignore % Iterators.fold_funspec single_term dummy dummy dummy []
  in
  Iterators.iter_funspec
    (single_term comp result_region)
    (single_assertion comp)
    single_location
    single_location_set
    spec;
  unify_logic_apps_in_funspec spec

let code_function comp f =
  let f, _, spec, body = IntHashtblIter.find Typing.functions_table f.fun_tag in
  Options.lprintf "Separation: treating function %s@." f.fun_name;
  let result_region = f.fun_return_region in
  funspec [] result_region spec;
  Option.iter (expr comp [] result_region) body

let code_component comp =
  let generalize_code_function f =
    let param_regions = List.map (fun (_, vi) -> vi.vi_region) f.fun_parameters in
    let fun_regions = f.fun_return_region :: param_regions in
    f.fun_param_regions <- RegionList.reachable fun_regions
  in
  (* Perform plain unification on component *)
  List.iter (code_function comp) comp;
  (* Generalize regions accessed *)
  List.iter generalize_code_function comp;
  (* Fill in association table at each call site *)
  List.iter (code_function []) comp

let prop comp _id (_loc, _is_axiom, _, _labels, a) = assertion comp dummy_region a

let regionalize_assertion a assoc =
  Iterators.map_term_in_assertion
    (fun t ->
       let t =
         match t#node with
         | JCTapp app ->
           let app_assoc =
             List.map
               (fun (rdist, rloc) ->
                  try
                    rdist, RegionList.assoc rloc assoc
                  with
                  | Not_found -> rdist, rloc)
               app.app_region_assoc
           in
           let tnode = JCTapp { app with app_region_assoc = app_assoc } in
           new term_with ~node:tnode t
         | JCTconst _      | JCTvar _     | JCTshift _
         | JCTderef _      | JCTbinary _  | JCTunary _        | JCTold _        | JCTat _        | JCToffset _
         | JCTaddress _    | JCTbase_block _
         | JCTinstanceof _ | JCTdowncast _                    | JCTsidecast _
         | JCTrange_cast _ | JCTrange_cast_mod _
         | JCTreal_cast _  | JCTif _
         | JCTmatch _      | JCTrange _   | JCTlet _ -> t
       in
       try
         new term_with ~region:(RegionList.assoc t#region assoc) t
       with
       | Not_found -> t)
    a

(*
Local Variables:
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End:
*)
