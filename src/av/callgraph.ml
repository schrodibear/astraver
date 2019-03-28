(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
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
open Ast
open Fenv

open Common

let term acc t =
  Iterators.fold_term
    (fun acc t -> match t#node with
    | JCTapp app -> app.app_fun::acc
    | _ -> acc
    ) acc t

let tag acc t = match t#node with
  | JCTtag _ | JCTbottom -> acc
  | JCTtypeof(t, _) -> term acc t

let rec assertion acc p =
  match p#node with
  | JCAtrue
  | JCAfalse -> acc
  | JCAfresh(_,_,t1,t2)
  | JCArelation(t1,_,t2) ->
      term (term acc t1) t2
  | JCAapp app -> app.app_fun :: (List.fold_left term acc app.app_args)
  | JCAand(pl) | JCAor(pl) -> List.fold_left assertion acc pl
  | JCAimplies (p1,p2) | JCAiff(p1,p2) ->
      assertion (assertion acc p1) p2
  | JCAif(t1,p2,p3) ->
      assertion (assertion (term acc t1) p2) p3
  | JCAnot p | JCAold p | JCAat(p,_) ->
      assertion acc p
  | JCAquantifier (_,_,trigs,p) -> triggers (assertion acc p) trigs
  | JCAinstanceof(t,_,_)
  | JCAmutable(t,_,_)
  | JCAbool_term t
  | JCAfreeable (_, t)
  | JCAallocable (_, t) -> term acc t
  | JCAeqtype(t1, t2, _) | JCAsubtype(t1, t2, _) ->
      tag (tag acc t1) t2
  | JCAlet(_,t, p) ->
      assertion (term acc t) p
  | JCAmatch(t, pal) ->
      term (List.fold_left (fun acc (_, a) -> assertion acc a) acc pal) t

and triggers acc trigs =
  List.fold_left (List.fold_left
    (fun acc pat -> match pat with
       | JCAPatT t -> term acc t
       | JCAPatP p -> assertion acc p)) acc trigs

(*
let spec s =
  begin
  match s.requires with
    | None -> []
    | Some p ->
	predicate p
  end @
  begin
  match s.assigns with
    | None -> []
    | Some l -> List.fold_left (fun acc t -> (term t) @acc)  [] l
  end @
  begin
    match s.ensures with
      | None -> []
      | Some p -> predicate p
  end @
  begin
    match s.decreases with
      | None -> []
      | Some (t,_) -> term t
  end
*)

let loop_annot acc la =
  let acc =
    List.fold_left
      (fun acc (_id,inv,_assigns) ->
	 (* TODO : traverse assigns clause *)
	 Option.fold ~f:assertion ~init:acc inv)
      acc la.loop_behaviors
  in
  match la.loop_variant with
  | None -> acc
  | Some (t,None) -> term acc t
  | Some (t,Some ri) -> term (ri::acc) t

let expr =
  Iterators.IExpr.fold_left
    (fun acc e -> match e#node with
       | JCEapp call ->
	   let f = call.call_fun in
	   let (a,b)=acc in
	   begin match f with
	     | JCfun f -> (a,f::b)
	     | JClogic_fun f -> (f::a,b)
	   end
       | JCEloop(spec,_s) ->
	   let (a,b) = acc in (loop_annot a spec,b)
       | _ -> acc
    )

let axiomatic_calls_table = Hashtbl.create 17

let compute_axiomatic_decl_call acc (Typing.ADprop (_, _, _, _, a)) = assertion acc a

let compute_axiomatic_calls a =
  try
    Hashtbl.find axiomatic_calls_table a
  with Not_found ->
    try
      let l = StringHashtblIter.find Typing.axiomatics_table a in
      let c = List.fold_left compute_axiomatic_decl_call [] l.Typing.axiomatics_decls in
      Hashtbl.add axiomatic_calls_table a c;
      c
    with
	Not_found -> assert false

let compute_logic_calls f t =
  let calls =
    match t with
      | JCTerm t -> term [] t
      | JCAssertion a -> assertion [] a
      | JCNone
      | JCReads _ ->
	  begin
	    match f.li_axiomatic with
	      | None -> []
	      | Some a -> compute_axiomatic_calls a
	  end
      | JCInductive l ->
	  List.fold_left (fun acc (_,_,a) -> assertion acc a) [] l
  in
  f.li_calls <- calls

let compute_calls f _s b =
  let (_a,b) = expr ([],[]) b in
  f.fun_calls <- b

module LogicCallGraph = struct
  type t = (Fenv.logic_info * Fenv.term_or_assertion) IntHashtblIter.t
  module V = struct
    type t = logic_info
    let compare f1 f2 = Pervasives.compare f1.li_tag f2.li_tag
    let hash f = f.li_tag
    let equal f1 f2 = f1 == f2
  end
  let iter_vertex iter =
    IntHashtblIter.iter (fun _ (f,_a) -> iter f)
  let iter_succ iter _ f =
    List.iter iter f.li_calls
  end

module LogicCallComponents = Graph.Components.Make(LogicCallGraph)

module CallGraph = struct
  type t = (fun_info * Loc.position * fun_spec * expr option) IntHashtblIter.t
  module V = struct
    type t = fun_info
    let compare f1 f2 = Pervasives.compare f1.fun_tag f2.fun_tag
    let hash f = f.fun_tag
    let equal f1 f2 = f1 == f2
  end
  let iter_vertex iter =
    IntHashtblIter.iter (fun _ (f,_loc,_spec,_b) -> iter f)
  let iter_succ iter _ f =
    List.iter iter f.fun_calls
  end

module CallComponents = Graph.Components.Make(CallGraph)

open Format
open Pp

let compute_logic_components ltable =
  let tab_comp = LogicCallComponents.scc_array ltable in
  Options.lprintf "***********************************\n";
  Options.lprintf "Logic call graph: has %d components\n"
    (Array.length tab_comp);
  Options.lprintf "***********************************\n";
  Array.iteri
    (fun i l ->
       Options.lprintf "Component %d:\n%a@." i
	 (print_list newline
	    (fun fmt f -> fprintf fmt " %s calls: %a\n" f.li_name
		 (print_list comma
		    (fun fmt f -> fprintf fmt "%s" f.li_name))
		 f.li_calls))
	 l)
    tab_comp;
  tab_comp


let compute_components table =
  (* see above *)
  let tab_comp = CallComponents.scc_array table in
  Options.lprintf "******************************\n";
  Options.lprintf "Call graph: has %d components\n" (Array.length tab_comp);
  Options.lprintf "******************************\n";
  Array.iteri
    (fun i l ->
      Options.lprintf "Component %d:\n%a@." i
	(print_list newline
	   (fun fmt f -> fprintf fmt " %s calls: %a\n" f.fun_name
	       (print_list comma
		  (fun fmt f -> fprintf fmt "%s" f.fun_name))
	       f.fun_calls))
	l)
    tab_comp;
  tab_comp
