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

open Java_env
open Java_tast

let rec term acc t =
  match t.java_term_node with
    | JTlit _ | JTvar _ 
    | JTstatic_field_access _ -> acc
    | JTapp (f,lt) -> f::(List.fold_left term acc lt)
    | JTold t -> term acc t
    | JTbin (t1,_,_,t2) -> term (term acc t1) t2
(*
    | JTif(t1,t2,t3) -> term (term (term acc t1) t2) t3
    | JTcast(t,_)
    | JTinstanceof(t,_)
    | JTunary (_,t) -> term acc t
*)
    | JTarray_access (t1, t2) -> term (term acc t1) t2
    | JTarray_length t1
    | JTfield_access (t1, _) -> term acc t1

let rec assertion acc p =
  match p.java_assertion_node with
  | JAtrue 
  | JAfalse -> acc
  | JAbin(t1,_,op,t2) -> term (term acc t1) t2
  | JAapp(f,lt) -> f::(List.fold_left term acc lt)
  | JAand(p1,p2) | JAor(p1,p2) 
  | JAimpl (p1,p2) | JAiff(p1,p2) -> 
      assertion (assertion acc p1) p2
(*
  | JAif(t1,p2,p3) -> 
      assertion (assertion (term acc t1) p2) p3
  | JAnot p 
  | JAold p 
  | JAinstanceof(t,_)
*)
  | JAquantifier (_,_,p) -> assertion acc p
  | JAbool_expr t -> term acc t

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

let rec expr acc e : 'a list = 
  match e.java_expr_node with
    | JElit _ 
    | JEvar _ 
    | JEincr_local_var _ 
    | JEstatic_field_access _ -> acc
    | JEcall (e, mi, args) ->
	List.fold_left expr (Option_misc.fold_left expr acc e) args
    | JEassign_array_op (e1, e2, _, e3)-> 
	expr (expr (expr acc e1) e2) e3
    | JEassign_local_var_op (_, _, e) 
    | JEassign_local_var (_, e) 
    | JEarray_length e  
    | JEfield_access (e, _) 
    | JEun (_, e) -> expr acc e 
    | JEassign_field (e1, _, e2)
    | JEassign_field_op (e1, _, _, e2)
    | JEarray_access (e1, e2) 
    | JEbin (e1, _, e2) -> expr (expr acc e1) e2

let initialiser acc i =
  match i with
    | JIexpr e -> expr acc e
    | _ -> assert false (* TODO *)

(*
let loop_annot acc la = 
  term (assertion acc la.java_loop_invariant) la.java_loop_variant
*)


let rec statement acc s : ('a list * 'b list) = 
  match s.java_statement_node with  
(*
*)
(*
    | JSthrow e 
*)
    | JSif(_, s1, s2) ->
	statement (statement acc s1) s2
(*
    | JSloop(spec,s) ->
	let (a,b) = statement acc s in (loop_annot a spec,b)
*)
    | JSblock sl -> 
	List.fold_left statement acc sl
(*
    | JStry (s, catches, finally) -> 
	let acc =
	  List.fold_left 
	    (fun acc (_,_,s) -> statement acc s) 
	    (statement acc s) catches
	in statement acc finally
*)
(*
    | JSdecl(vi,_,s) -> 
	statement acc s
*)
    | JSassert (_,t) -> let (a,b) = acc in (assertion a t,b)
    | JSbreak _ -> acc 
    | JSswitch (e, l)-> 
	let (a,b) = acc in
	let b = expr b e in
	List.fold_left
	  (fun acc (cases,body) -> statements acc body)
	  (a,b) l
    | JSreturn e 
    | JSexpr e -> let (a,b)=acc in (a,expr b e)
    | JSfor_decl (inits, cond, inv, dec, updates, body)-> 
	let (a,b) = acc in
	let b = List.fold_left 
	  (fun acc (vi,i) -> Option_misc.fold_left initialiser acc i)
	  (List.fold_left expr (expr b cond) updates)
	  inits
	in
	let a = term (assertion a inv) dec in
	statement (a,b) body
	
    | JSwhile (cond, inv, dec, body)-> 
	let (a,b) = acc in
	let b = expr b cond in
	let a = term (assertion a inv) dec in
	statement (a,b) body
    | JSvar_decl (vi, init, s)-> 
	let (a,b)=acc in
	statement (a,Option_misc.fold_left initialiser b init) s
    | JSskip -> acc

and statements acc l = List.fold_left statement acc l

let compute_logic_calls f t = 
  let calls =
    match t with
      | Java_typing.JTerm t -> term [] t 
      | Java_typing.JAssertion a -> assertion [] a 
(*
      | JReads r -> []
*)
  in
  f.java_logic_info_calls <- calls

let compute_calls f s b = 
  let (a,b) = List.fold_left statement ([],[]) b in
  f.method_info_calls <- b

      
module LogicCallGraph = struct 
  type t = (int, (java_logic_info * Java_typing.logic_body)) Hashtbl.t 
  module V = struct
    type t = java_logic_info
    let compare f1 f2 = Pervasives.compare f1.java_logic_info_tag f2.java_logic_info_tag
    let hash f = f.java_logic_info_tag
    let equal f1 f2 = f1 == f2
  end
  let iter_vertex iter =
    Hashtbl.iter (fun _ (f,a) -> iter f) 
  let iter_succ iter _ f =
    List.iter iter f.java_logic_info_calls 
  end

module LogicCallComponents = Graph.Components.Make(LogicCallGraph)

module CallGraph = struct 
  type t = (int, Java_typing.method_table_info) Hashtbl.t
  module V = struct
    type t = method_info
    let compare f1 f2 = Pervasives.compare f1.method_info_tag f2.method_info_tag
    let hash f = f.method_info_tag
    let equal f1 f2 = f1 == f2
  end
  let iter_vertex iter =
    Hashtbl.iter (fun _ mti -> iter mti.Java_typing.mt_method_info) 
  let iter_succ iter _ f =
    List.iter iter f.method_info_calls 
  end

module CallComponents = Graph.Components.Make(CallGraph)

open Format
open Pp

let compute_logic_components ltable =  
  let tab_comp = LogicCallComponents.scc_array ltable in
  Java_options.lprintf "***********************************\n";
  Java_options.lprintf "Logic call graph: has %d components\n" 
    (Array.length tab_comp);
  Java_options.lprintf "***********************************\n";
  Array.iteri 
    (fun i l -> 
       Java_options.lprintf "Component %d:\n%a@." i
	 (print_list newline 
	    (fun fmt f -> fprintf fmt " %s calls: %a\n" f.java_logic_info_name
		 (print_list comma 
		    (fun fmt f -> fprintf fmt "%s" f.java_logic_info_name))
		 f.java_logic_info_calls))
	 l)
    tab_comp;
  tab_comp


let compute_components table =  
  let tab_comp = CallComponents.scc_array table in
  Java_options.lprintf "******************************\n";
  Java_options.lprintf "Call graph: has %d components\n" (Array.length tab_comp);
  Java_options.lprintf "******************************\n";
  Array.iteri 
    (fun i l -> 
       Java_options.lprintf "Component %d:\n%a@." i
	 (print_list newline 
	    (fun fmt f -> fprintf fmt " %s calls: %a\n" f.method_info_name
		 (print_list comma 
		    (fun fmt f -> fprintf fmt "%s" f.method_info_name))
		 f.method_info_calls))
	 l)
    tab_comp;
  tab_comp




(*
Local Variables: 
compile-command: "make -j -C .. bin/krakatoa.byte"
End: 
*)
