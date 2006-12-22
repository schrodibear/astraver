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
    | JCToffset_max t | JCToffset_min t
    | JCTold t | JCTderef (t,_) -> term acc t
    | JCTshift (t1,t2) -> term (term acc t1) t2
    | JCTif(t1,t2,t3) -> term (term (term acc t1) t2) t3
    | JCTcast(t,_)
    | JCTinstanceof(t,_) -> term acc t

let rec assertion acc p =
  match p.jc_assertion_node with
  | JCAtrue 
  | JCAfalse -> acc
  | JCAapp(f,lt) -> f::(List.fold_left term acc lt)
  | JCAand(pl) -> List.fold_left assertion acc pl
  | JCAimplies (p1,p2) | JCAiff(p1,p2) -> 
      assertion (assertion acc p1) p2
  | JCAif(t1,p2,p3) -> 
      assertion (assertion (term acc t1) p2) p3
  | JCAnot p | JCAold p | JCAforall (_,p) -> assertion acc p
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

let rec expr acc e =
  match e.jc_expr_node with 
    | JCEconst _ | JCEvar _ | JCEincr_local _ -> acc
    | JCEderef(e, _) 
    | JCEinstanceof(e,_)
    | JCEcast(e,_)
    | JCEassign_local (_, e) 
    | JCEassign_op_local(_, _, e) 
    | JCEincr_heap (_, _, e) -> expr acc e
    | JCEshift (e1,e2) 
    | JCEassign_heap (e1,_, e2)
    | JCEassign_op_heap(e1,_, _, e2) -> expr (expr acc e1) e2
    | JCEif(e1,e2,e3) -> expr (expr (expr acc e1) e2) e3
    | JCEcall (f, le) -> 
	f::(List.fold_left expr acc le)

let rec statement acc s = 
  match s.jc_statement_node with  
    | JCSreturn e 
    | JCSpack(_,e) | JCSunpack(_,e)
    | JCSexpr e -> let (a,b)=acc in (a,expr b e)
    | JCSif(e, s1, s2) ->
	let (a,b) = statement (statement acc s1) s2 in (a,expr b e)
    | JCSwhile(e,spec,s) ->
	let (a,b) = statement acc s in (loop_annot a spec,expr b e)
    | JCSblock sl -> 
	List.fold_left statement acc sl
    | JCSthrow (ei, e) -> let (a,b)=acc in (a,expr b e)
    | JCStry (s, catches, finally) -> 
	let acc =
	  List.fold_left 
	    (fun acc (_,_,s) -> statement acc s) 
	    (statement acc s) catches
	in statement acc finally
    | JCSgoto _ -> assert false (* TODO *)
    | JCScontinue _ -> assert false (* TODO *)
    | JCSbreak _  -> assert false (* TODO *)
    | JCSdecl(vi,e,s) -> 
	let (a,b)=acc in statement (a,Option_misc.fold_left expr b e) s
    | JCSassert _ -> assert false (* TODO *)


let compute_logic_calls f t = 
  let calls =
    match t with
      | JCTerm t -> term [] t 
      | JCAssertion a -> assertion [] a 
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
  type t = (int, (fun_info * fun_spec * statement list)) Hashtbl.t
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
