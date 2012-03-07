(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
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

open Java_env
open Java_tast

let rec term acc t =
  match t.java_term_node with
    | JTlit _ | JTvar _
    | JTstatic_field_access _ -> acc
    | JTapp (f,_labs,lt) -> f::(List.fold_left term acc lt)
    | JTat(t,_) -> term acc t
    | JTbin (t1,_,_,t2) -> term (term acc t1) t2
    | JTbin_obj (t1,_,t2) -> term (term acc t1) t2
    | JTun (_,_,t1) -> term acc t1
    | JTif(t1,t2,t3) -> term (term (term acc t1) t2) t3
(*
    | JTinstanceof(t,_)
    | JTunary (_,t)
*)
    | JTcast(_,t) -> term acc t
    | JTarray_access (t1, t2) -> term (term acc t1) t2
    | JTarray_range (t1, t2, t3) ->
	Option_misc.fold_left term
	  (Option_misc.fold_left term (term acc t1) t2) t3
    | JTarray_length t1
    | JTfield_access (t1, _) -> term acc t1

let rec assertion acc p =
  match p.java_assertion_node with
  | JAtrue
  | JAfalse -> acc
  | JAat(a,_lab) -> assertion acc a
  | JAnot a -> assertion acc a
  | JAbin_obj(t1,_,t2)
  | JAbin(t1,_,_,t2) -> term (term acc t1) t2
  | JAapp(f,_labs,lt) -> f::(List.fold_left term acc lt)
  | JAand(p1,p2) | JAor(p1,p2)
  | JAimpl (p1,p2) | JAiff(p1,p2) ->
      assertion (assertion acc p1) p2
  | JAif(t1,p2,p3) ->
      assertion (assertion (term acc t1) p2) p3
  | JAquantifier (_,_,p) -> assertion acc p
  | JAfresh t | JAbool_expr t | JAinstanceof (t, _, _) -> term acc t


let rec expr acc e : 'a list =
  match e.java_expr_node with
    | JElit _
    | JEvar _
    | JEincr_local_var _
    | JEstatic_field_access _ -> acc
    | JEcall (e, mi, args) ->
	List.fold_left expr (expr (MethodInfo mi::acc) e) args
    | JEconstr_call (e, ci, args) ->
	List.fold_left expr (expr (ConstructorInfo ci::acc) e) args
    | JEstatic_call (mi, args) ->
	List.fold_left expr (MethodInfo mi::acc) args
    | JEnew_array(_ty, dims) ->
	List.fold_left expr acc dims
    | JEnew_object(ci,args) ->
	List.fold_left expr (ConstructorInfo ci::acc) args
    | JEif(e1,e2,e3)
    | JEassign_array (e1, e2, e3)
    | JEassign_array_op (e1, e2, _, e3)->
	expr (expr (expr acc e1) e2) e3
    | JEassign_local_var_op (_, _, e)
    | JEassign_local_var (_, e)
    | JEassign_static_field ( _, e)
    | JEassign_static_field_op ( _, _, e)
    | JEarray_length e
    | JEfield_access (e, _)
    | JEincr_field (_,e,_)
    | JEun (_, e) -> expr acc e
    | JEassign_field (e1, _, e2)
    | JEassign_field_op (e1, _, _, e2)
    | JEarray_access (e1, e2)
    | JEbin (e1, _, e2) | JEincr_array (_, e1, e2) ->
	expr (expr acc e1) e2
    | JEinstanceof(e,_)
    | JEcast (_,e) -> expr acc e

let initialiser acc i =
  match i with
    | JIexpr e -> expr acc e
    | _ -> assert false (* TODO *)

(*
let loop_annot acc la =
  term (assertion acc la.java_loop_invariant) la.java_loop_variant
*)

let behavior acc (_id,assumes,_throws,assigns,allocates,ensures) =
  let acc = Option_misc.fold_left assertion acc assumes in
  let acc =
    match assigns with
      | None -> acc
      | Some(_,l) -> List.fold_left term acc l
  in
  let acc =
    match allocates with
      | None -> acc
      | Some(_,l) -> List.fold_left term acc l
  in
  assertion acc ensures

let variant acc v =
  match v with
    | None -> acc
    | Some(dec,None) -> term acc dec
    | Some(dec,Some fi) -> term (fi::acc) dec

let loop_annot acc annot =
  let acc = assertion acc annot.loop_inv in
  let acc =
    List.fold_left (fun acc (_,a) -> assertion acc a) acc annot.behs_loop_inv
  in
  variant acc annot.loop_var

let rec statement acc s : ('a list * 'b list) =
  match s.java_statement_node with
    | JSif(e, s1, s2) ->
	let (a,b) = acc in
	let b = expr b e in
	  statement (statement (a,b) s1) s2
    | JSblock sl ->
	List.fold_left statement acc sl
    | JStry (s, catches, finally) ->
	let acc = List.fold_left statement acc s in
	let acc =
	  List.fold_left
	    (fun acc (_,s) -> List.fold_left statement acc s)
	    acc catches
	in
	  Option_misc.fold
	    (fun b acc -> List.fold_left statement acc b) finally acc
    | JSassert(_,_,t) -> let (a,b) = acc in (assertion a t,b)
    | JSreturn_void
    | JSbreak _ -> acc
    | JScontinue _ -> acc
    | JSlabel(_lab,s) ->	statement acc s
    | JSswitch (e, l)->
	let (a,b) = acc in
	let b = expr b e in
	  List.fold_left
	    (fun acc (_cases,body) -> statements acc body)
	    (a,b) l
    | JSthrow e
    | JSreturn e
    | JSexpr e -> let (a, b) = acc in (a, expr b e)
    | JSfor (inits, cond, annot, updates, body)->
	let (a, b) = acc in
	let b = List.fold_left expr
	  (List.fold_left expr (expr b cond) updates)
	  inits
	in
	let a = loop_annot a annot in
	statement (a, b) body
    | JSfor_decl (inits, cond, annot, updates, body)->
	let (a,b) = acc in
	let b = List.fold_left
	  (fun acc (_vi,i) -> Option_misc.fold_left initialiser acc i)
	  (List.fold_left expr (expr b cond) updates)
	  inits
	in
	let a = loop_annot a annot in
	statement (a,b) body
    | JSdo (body, annot, cond)->
	let a, b = acc in
	let a, b = statement (a, b) body in
	let a = loop_annot a annot in
	let b = expr b cond in
	a, b
    | JSwhile (cond, annot, body)->
	let (a,b) = acc in
	let b = expr b cond in
	let a = loop_annot a annot in
	statement (a,b) body
    | JSvar_decl (_vi, init, s)->
	let (a,b)=acc in
	statement (a,Option_misc.fold_left initialiser b init) s
    | JSskip -> acc
    | JSstatement_spec(req,dec,behs,s) ->
	let (a,b) = acc in
	let a = Option_misc.fold_left assertion a req in
	let a = variant a dec in
	let a = List.fold_left behavior a behs in
	statement (a,b) s

and statements acc l = List.fold_left statement acc l

let compute_logic_calls f (t : [< Java_typing.logic_decl_body]) =
  let calls =
    match t with
      | `Term t -> term [] t
      | `Assertion a -> assertion [] a
      | `None -> []
      | `Reads r -> List.fold_left term [] r
      | `Inductive l ->
	  List.fold_left
	    (fun acc (_,_,a) -> assertion acc a) [] l
      | `Builtin -> []
  in
  f.java_logic_info_calls <- calls

let compute_calls f _req body =
  let (_a, b) = List.fold_left statement ([], []) body in
    f.method_info_calls <- b

let compute_constr_calls f _req body =
  let (_a, b) = List.fold_left statement ([], []) body in
    f.constr_info_calls <- b

module LogicCallGraph = struct
  type t = (int, (java_logic_info * Java_typing.logic_def_body)) Hashtbl.t
  module V = struct
    type t = java_logic_info
    let compare f1 f2 = Pervasives.compare f1.java_logic_info_tag f2.java_logic_info_tag
    let hash f = f.java_logic_info_tag
    let equal f1 f2 = f1 == f2
  end
  let iter_vertex iter =
    Hashtbl.iter (fun _ (f,_a) -> iter f)
  let iter_succ iter _ f =
    List.iter iter f.java_logic_info_calls
  end

module LogicCallComponents = Graph.Components.Make(LogicCallGraph)

open Format
open Pp


type method_or_constructor_data =
  | MethodData of Java_typing.method_table_info
  | ConstructorData of Java_typing.constructor_table_info

let method_or_constructor_tag x =
  match x with
    | MethodInfo mi -> mi.method_info_tag
    | ConstructorInfo ci -> ci.constr_info_tag

let method_or_constructor_info mt =
  match mt with
    | MethodData mti -> MethodInfo mti.Java_typing.mt_method_info
    | ConstructorData cti -> ConstructorInfo cti.Java_typing.ct_constr_info

let print_method_or_constr fmt f =
  match f with
    | MethodInfo fi ->
	fprintf fmt "%a.%s" Java_typing.print_type_name
	  fi.method_info_class_or_interface fi.method_info_name
    | ConstructorInfo ci -> fprintf fmt "%s" ci.constr_info_trans_name

let method_or_constr_calls f =
  match f with
    | MethodInfo fi -> fi.method_info_calls
    | ConstructorInfo ci -> ci.constr_info_calls


module CallGraph = struct
  type t = (int, method_or_constructor_data) Hashtbl.t
  module V = struct
    type t = method_or_constructor_info

    let compare f1 f2 =
      Pervasives.compare
	(method_or_constructor_tag f1) (method_or_constructor_tag f2)

    let hash f = method_or_constructor_tag f
    let equal f1 f2 = method_or_constructor_tag f1 == method_or_constructor_tag f2
  end
  let iter_vertex iter g =
    Hashtbl.iter
      (fun _i mti ->
	 let f = method_or_constructor_info mti in
	 iter f) g
  let iter_succ iter _ f =
    List.iter iter
      (match f with
	 | MethodInfo fi -> fi.method_info_calls
	 | ConstructorInfo ci -> ci.constr_info_calls)
  end
module CallComponents = Graph.Components.Make(CallGraph)

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


let compute_components methods constrs =
  let h = Hashtbl.create 97 in
  Hashtbl.iter
    (fun _ mti ->
       Hashtbl.add h
	 mti.Java_typing.mt_method_info.method_info_tag (MethodData mti))
    methods;
  Hashtbl.iter
    (fun _ cti ->
       Hashtbl.add h
	 cti.Java_typing.ct_constr_info.constr_info_tag (ConstructorData cti))
    constrs;
  let _n,comp = CallComponents.scc h in
  let tab_comp = CallComponents.scc_array h in
  Java_options.lprintf "******************************@\n";
  Java_options.lprintf "Call graph: has %d components@\n" (Array.length tab_comp);
  Java_options.lprintf "******************************@\n";
  Array.iteri
    (fun i l ->
       Java_options.lprintf "Component %d:@\n%a@." i
	 (print_list newline
	    (fun fmt f -> fprintf fmt " - %a calls: %a@\n"
	       print_method_or_constr f
	       (print_list comma
		  (fun fmt f -> fprintf fmt "%a(%d)"
		     print_method_or_constr f (comp f)))
	       (method_or_constr_calls f)))
	 l)
    tab_comp;
  tab_comp




(*
Local Variables:
compile-command: "make -j -C .. bin/krakatoa.byte"
End:
*)
