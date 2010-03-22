(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Jc_stdlib
open Jc_env
open Jc_ast
open Jc_fenv

open Jc_pervasives

let rec term acc t =
  Jc_iterators.fold_term 
    (fun acc t -> match t#node with
    | JCTapp app -> app.jc_app_fun::acc
    | _ -> acc
    ) acc t

let tag acc t = match t#node with
  | JCTtag _ | JCTbottom -> acc
  | JCTtypeof(t, _) -> term acc t

let rec assertion acc p =
  match p#node with
  | JCAtrue 
  | JCAfalse -> acc
  | JCArelation(t1,_op,t2) ->
      term (term acc t1) t2
  | JCAapp app -> app.jc_app_fun :: (List.fold_left term acc app.jc_app_args)
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
  | JCAbool_term t -> term acc t
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
	 Option_misc.fold_left assertion acc inv)
      acc la.jc_loop_behaviors 
  in
  match la.jc_loop_variant with
  | None -> acc
  | Some (t,None) -> term acc t
  | Some (t,Some ri) -> term (ri::acc) t

let expr = 
  Jc_iterators.IExpr.fold_left 
    (fun acc e -> match e#node with  
       | JCEapp call ->
	   let f = call.jc_call_fun in
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

let compute_axiomatic_decl_call acc d =
  match d with
    | Jc_typing.ABaxiom(_,_,_,a) -> assertion acc a

let compute_axiomatic_calls a =
  try
    Hashtbl.find axiomatic_calls_table a
  with Not_found ->
    try
      let l = Hashtbl.find Jc_typing.axiomatics_table a in
      let c = List.fold_left compute_axiomatic_decl_call [] l.Jc_typing.axiomatics_decls in
      Hashtbl.add axiomatic_calls_table a c;
      c
    with
	Not_found -> assert false

let compute_logic_calls f t = 
  let calls =
    match t with
      | JCNone -> []
      | JCTerm t -> term [] t 
      | JCAssertion a -> assertion [] a 
      | JCReads _r -> 
	  begin
	    match f.jc_logic_info_axiomatic with
	      | None -> []
	      | Some a -> compute_axiomatic_calls a 
	  end
      | JCInductive l -> 
	  List.fold_left (fun acc (_,_,a) -> assertion acc a) [] l
  in
  f.jc_logic_info_calls <- calls

let compute_calls f _s b = 
  let (_a,b) = expr ([],[]) b in
  f.jc_fun_info_calls <- b
      
module LogicCallGraph = struct 
  type t = (int, (Jc_fenv.logic_info * Jc_fenv.term_or_assertion)) Hashtbl.t 
  module V = struct
    type t = logic_info
    let compare f1 f2 = Pervasives.compare f1.jc_logic_info_tag f2.jc_logic_info_tag
    let hash f = f.jc_logic_info_tag
    let equal f1 f2 = f1 == f2
  end
  let iter_vertex iter =
    Hashtbl.iter (fun _ (f,_a) -> iter f) 
  let iter_succ iter _ f =
    List.iter iter f.jc_logic_info_calls 
  end

module LogicCallComponents = Graph.Components.Make(LogicCallGraph)

module CallGraph = struct 
  type t = (int, (fun_info * Loc.position * fun_spec * expr option)) Hashtbl.t
  module V = struct
    type t = fun_info
    let compare f1 f2 = Pervasives.compare f1.jc_fun_info_tag f2.jc_fun_info_tag
    let hash f = f.jc_fun_info_tag
    let equal f1 f2 = f1 == f2
  end
  let iter_vertex iter =
    Hashtbl.iter (fun _ (f,_loc,_spec,_b) -> iter f) 
  let iter_succ iter _ f =
    List.iter iter f.jc_fun_info_calls 
  end

module CallComponents = Graph.Components.Make(CallGraph)

open Format
open Pp

let compute_logic_components :
 (int, Jc_fenv.logic_info * Jc_fenv.term_or_assertion) Hashtbl.t ->
    Jc_fenv.logic_info list array = fun ltable ->  
  let tab_comp = LogicCallComponents.scc_array ltable in
  Jc_options.lprintf "***********************************\n";
  Jc_options.lprintf "Logic call graph: has %d components\n" 
    (Array.length tab_comp);
  Jc_options.lprintf "***********************************\n";
  Array.iteri 
    (fun i l -> 
       Jc_options.lprintf "Component %d:\n%a@." i
	 (print_list newline 
	    (fun fmt f -> fprintf fmt " %s calls: %a\n" f.jc_logic_info_name
		 (print_list comma 
		    (fun fmt f -> fprintf fmt "%s" f.jc_logic_info_name))
		 f.jc_logic_info_calls))
	 l)
    tab_comp;
  tab_comp


let compute_components table = 
  (* see above *)
  let tab_comp = CallComponents.scc_array table in
  Jc_options.lprintf "******************************\n";
  Jc_options.lprintf "Call graph: has %d components\n" (Array.length tab_comp);
  Jc_options.lprintf "******************************\n";
  Array.iteri 
    (fun i l -> 
      Jc_options.lprintf "Component %d:\n%a@." i
	(print_list newline 
	   (fun fmt f -> fprintf fmt " %s calls: %a\n" f.jc_fun_info_name
	       (print_list comma 
		  (fun fmt f -> fprintf fmt "%s" f.jc_fun_info_name))
	       f.jc_fun_info_calls))
	l)
    tab_comp;
  tab_comp
    
    


(*
Local Variables: 
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*)
