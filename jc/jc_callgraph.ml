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

open Jc_env
open Jc_fenv
open Jc_ast

let rec term acc t =
  match t.jc_term_node with
    | JCTconst _ 
    | JCTvar _ -> acc
    | JCTapp (f,lt) -> f::(List.fold_left term acc lt)
    | JCToffset_max(t,_) | JCToffset_min(t,_)
    | JCTold t | JCTderef (t,_) -> term acc t
    | JCTshift (t1,t2) 
    | JCTrange (t1,t2)
    | JCTbinary (t1,_,t2) -> term (term acc t1) t2
    | JCTif(t1,t2,t3) -> term (term (term acc t1) t2) t3
    | JCTcast(t,_)
    | JCTinstanceof(t,_)
    | JCTunary (_,t) -> term acc t

let rec assertion acc p =
  match p.jc_assertion_node with
  | JCAtrue 
  | JCAfalse -> acc
  | JCArelation(t1,op,t2) ->
      term (term acc t1) t2
  | JCAapp(f,lt) -> f::(List.fold_left term acc lt)
  | JCAand(pl) | JCAor(pl) -> List.fold_left assertion acc pl
  | JCAimplies (p1,p2) | JCAiff(p1,p2) -> 
      assertion (assertion acc p1) p2
  | JCAif(t1,p2,p3) -> 
      assertion (assertion (term acc t1) p2) p3
  | JCAnot p | JCAold p | JCAforall (_,p) | JCAexists (_,p) -> assertion acc p
  | JCAinstanceof(t,_)
  | JCAbool_term t -> term acc t

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
  term (assertion acc la.jc_loop_invariant) la.jc_loop_variant

let rec statement acc s = 
  match s.jc_statement_node with  
    | JCScall (_, f, le, s) ->
	let (a,b)=acc in statement (a,f::b) s
    | JCSassign_local _ | JCSassign_heap _ -> acc
    | JCSreturn _ | JCSpack _ | JCSunpack _ | JCSthrow _ -> acc
    | JCSif(_, s1, s2) ->
	statement (statement acc s1) s2
    | JCSloop(spec,s) ->
	let (a,b) = statement acc s in (loop_annot a spec,b)
    | JCSblock sl -> 
	List.fold_left statement acc sl
    | JCStry (s, catches, finally) -> 
	let acc =
	  List.fold_left 
	    (fun acc (_,_,s) -> statement acc s) 
	    (statement acc s) catches
	in statement acc finally
    | JCSdecl(vi,_,s) -> 
	statement acc s
    | JCSassert _ -> acc

let compute_logic_calls f t = 
  let calls =
    match t with
      | JCTerm t -> term [] t 
      | JCAssertion a -> assertion [] a 
      | JCReads r -> []
  in
  f.jc_logic_info_calls <- calls

let compute_calls f s b = 
  let (a,b) = List.fold_left statement ([],[]) b in
  f.jc_fun_info_calls <- b

      
module LogicCallGraph = struct 
  type t = (int, (logic_info * term_or_assertion)) Hashtbl.t 
  module V = struct
    type t = logic_info
    let compare f1 f2 = Pervasives.compare f1.jc_logic_info_tag f2.jc_logic_info_tag
    let hash f = f.jc_logic_info_tag
    let equal f1 f2 = f1 == f2
  end
  let iter_vertex iter =
    Hashtbl.iter (fun _ (f,a) -> iter f) 
  let iter_succ iter _ f =
    List.iter iter f.jc_logic_info_calls 
  end

module LogicCallComponents = Components.Make(LogicCallGraph)

module CallGraph = struct 
  type t = (int, (fun_info * fun_spec * statement list option)) Hashtbl.t
  module V = struct
    type t = fun_info
    let compare f1 f2 = Pervasives.compare f1.jc_fun_info_tag f2.jc_fun_info_tag
    let hash f = f.jc_fun_info_tag
    let equal f1 f2 = f1 == f2
  end
  let iter_vertex iter =
    Hashtbl.iter (fun _ (f,spec,b) -> iter f) 
  let iter_succ iter _ f =
    List.iter iter f.jc_fun_info_calls 
  end

module CallComponents = Components.Make(CallGraph)

open Format
open Pp

let compute_logic_components ltable =  
  let (scc,numcomp) = LogicCallComponents.scc ltable in
  let tab_comp = Array.make numcomp [] in
  LogicCallGraph.iter_vertex 
    (fun f ->
       let i = scc f in 
       Array.set tab_comp i (f::(Array.get tab_comp i))) ltable ;
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
  let (scc,numcomp) = CallComponents.scc table in
  let tab_comp = Array.make numcomp [] in
  CallGraph.iter_vertex 
    (fun f ->
       let i = scc f in 
       Array.set tab_comp i (f::(Array.get tab_comp i))) table ;
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
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
