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

open Format
open Jc_env
open Jc_envset
open Jc_fenv
open Jc_ast
open Jc_pervasives


(*****************************************************************************)
(* General iterators on expressions.                                         *)
(*****************************************************************************)

let rec iter_expr f e =
  f e;
  match e.jc_expr_node with
    | JCEconst _ | JCEvar _ -> ()
    | JCEbinary(e1,_,e2) | JCEshift(e1,e2) | JCEsub_pointer(e1,e2) ->
	iter_expr f e1; iter_expr f e2
    | JCEunary(_,e1) | JCEderef(e1,_) | JCEoffset(_,e1,_) | JCEinstanceof(e1,_)
    | JCEcast(e1,_) | JCErange_cast(_,e1) | JCEalloc(e1,_) | JCEfree e1 ->
	iter_expr f e1
    | JCEif(e1,e2,e3) ->
	iter_expr f e1; iter_expr f e2; iter_expr f e3
  
let rec fold_expr f acc e =
  let acc = f acc e in
  match e.jc_expr_node with
    | JCEconst _ | JCEvar _ -> acc
    | JCEbinary(e1,_,e2) | JCEshift(e1,e2) | JCEsub_pointer(e1,e2) ->
	let acc = fold_expr f acc e1 in
	fold_expr f acc e2
    | JCEunary(_,e1) | JCEderef(e1,_) | JCEoffset(_,e1,_) | JCEinstanceof(e1,_)
    | JCEcast(e1,_) | JCErange_cast(_,e1) | JCEalloc(e1,_) | JCEfree e1 ->
	fold_expr f acc e1
    | JCEif(e1,e2,e3) ->
	let acc = fold_expr f acc e1 in
	let acc = fold_expr f acc e2 in
	fold_expr f acc e3


(*****************************************************************************)
(* General iterators on statements.                                          *)
(*****************************************************************************)

let rec iter_expr_and_statement fexpr fstat s =
  fstat s;
  match s.jc_statement_node with
    | JCSdecl(_,None,s) ->
	iter_expr_and_statement fexpr fstat s
    | JCSdecl(_,Some e,s) ->
	iter_expr fexpr e;
	iter_expr_and_statement fexpr fstat s
    | JCScall(_,call,s) -> 
	List.iter (iter_expr fexpr) call.jc_call_args;
	iter_expr_and_statement fexpr fstat s
    | JCSblock sl ->
	List.iter (iter_expr_and_statement fexpr fstat) sl
    | JCSif(e,ts,fs) ->
	iter_expr fexpr e;
	iter_expr_and_statement fexpr fstat ts;
	iter_expr_and_statement fexpr fstat fs
    | JCStry(s,hl,fs) ->
	iter_expr_and_statement fexpr fstat s;
	List.iter (fun (_,_,s) -> iter_expr_and_statement fexpr fstat s) hl;
	iter_expr_and_statement fexpr fstat fs
    | JCSloop(_,ls) ->
	iter_expr_and_statement fexpr fstat ls
    | JCSreturn(_,e) | JCSthrow(_,Some e) | JCSassign_var(_,e) 
    | JCSpack(_,e,_) | JCSunpack(_,e,_) ->
	iter_expr fexpr e
    | JCSassign_heap(e1,_,e2) ->
	iter_expr fexpr e1;
	iter_expr fexpr e2
    | JCSthrow(_,None) | JCSassert _ | JCSreturn_void ->
	()

let rec fold_statement fpre fpost acc s =
  let acc = fpre acc s in
  let acc = match s.jc_statement_node with
    | JCSdecl(_,_,s) | JCScall(_,_,s) -> 
	fold_statement fpre fpost acc s
    | JCSblock sl ->
	List.fold_left (fold_statement fpre fpost) acc sl
    | JCSif(_,ts,fs) ->
	let acc = fold_statement fpre fpost acc ts in
	fold_statement fpre fpost acc fs
    | JCStry(s,hl,fs) ->
	let acc = fold_statement fpre fpost acc s in
	let acc = 
	  List.fold_left (fun acc (_,_,s) -> 
	    fold_statement fpre fpost acc s
	  ) acc hl
	in
	fold_statement fpre fpost acc fs
    | JCSloop(_,ls) ->
	fold_statement fpre fpost acc ls
    | JCSreturn _ | JCSthrow _ | JCSassert _ | JCSassign_var _
    | JCSassign_heap _ | JCSpack _ | JCSunpack _ | JCSreturn_void ->
	acc
  in
  fpost acc s

let rec fold_expr_in_statement f acc s =
  match s.jc_statement_node with
    | JCSdecl(_,None,s) ->
	fold_expr_in_statement f acc s
    | JCSdecl(_,Some e,s) ->
	let acc = fold_expr f acc e in
	fold_expr_in_statement f acc s
    | JCScall(_,call,s) -> 
	let acc = List.fold_left (fold_expr f) acc call.jc_call_args in
	fold_expr_in_statement f acc s
    | JCSblock sl ->
	List.fold_left (fold_expr_in_statement f) acc sl
    | JCSif(e,ts,fs) ->
	let acc = fold_expr f acc e in
	let acc = fold_expr_in_statement f acc ts in
	fold_expr_in_statement f acc fs
    | JCStry(s,hl,fs) ->
	let acc = fold_expr_in_statement f acc s in
	let acc = 
	  List.fold_left 
	    (fun acc (_,_,s) -> fold_expr_in_statement f acc s) acc hl
	in
	fold_expr_in_statement f acc fs
    | JCSloop(_,ls) ->
	fold_expr_in_statement f acc ls
    | JCSreturn(_,e) | JCSthrow(_,Some e) | JCSassign_var(_,e) 
    | JCSpack(_,e,_) | JCSunpack(_,e,_) ->
	fold_expr f acc e
    | JCSassign_heap(e1,_,e2) ->
	let acc = fold_expr f acc e1 in
	fold_expr f acc e2
    | JCSthrow(_,None) | JCSassert _ | JCSreturn_void ->
	acc


(*****************************************************************************)
(* General iterators on terms.                                               *)
(*****************************************************************************)

let rec iter_term f t =
  f t;
  match t.jc_term_node with
  | JCTconst _ | JCTvar _ | JCTrange(None,None) -> ()
  | JCTbinary(t1,_,t2) | JCTshift(t1,t2) | JCTsub_pointer(t1,t2) 
  | JCTrange(Some t1,Some t2) ->
      iter_term f t1; iter_term f t2
  | JCTunary(_,t1) | JCTderef(t1,_) | JCTold t1 | JCToffset(_,t1,_)
  | JCTinstanceof(t1,_) | JCTcast(t1,_) | JCTrange(Some t1,None)
  | JCTrange(None,Some t1) ->
      iter_term f t1
  | JCTapp app ->
      let tl = app.jc_app_args in
      List.iter (iter_term f) tl
  | JCTif(t1,t2,t3) ->
      iter_term f t1; iter_term f t2; iter_term f t3

let rec fold_term f acc t =
  let acc = f acc t in
  match t.jc_term_node with
  | JCTconst _ | JCTvar _ | JCTrange(None,None) -> acc
  | JCTbinary(t1,_,t2) | JCTshift(t1,t2) | JCTsub_pointer(t1,t2) 
  | JCTrange(Some t1,Some t2) ->
      let acc = fold_term f acc t1 in
      fold_term f acc t2
  | JCTunary(_,t1) | JCTderef(t1,_) | JCTold t1 | JCToffset(_,t1,_)
  | JCTinstanceof(t1,_) | JCTcast(t1,_) | JCTrange(Some t1,None)
  | JCTrange(None,Some t1) ->
      fold_term f acc t1
  | JCTapp app ->
      let tl = app.jc_app_args in
      List.fold_left (fold_term f) acc tl
  | JCTif(t1,t2,t3) ->
      let acc = fold_term f acc t1 in
      let acc = fold_term f acc t2 in
      fold_term f acc t3

let rec map_term f t =
  let tnode = match t.jc_term_node with
    | JCTconst _ | JCTvar _ | JCTrange (None, None) as tnode -> tnode
    | JCTbinary(t1,bop,t2) ->
	JCTbinary(map_term f t1,bop,map_term f t2) 
    | JCTunary(uop,t1) ->
	JCTunary(uop,map_term f t1)
    | JCTshift(t1,t2) ->
	JCTshift(map_term f t1,map_term f t2)
    | JCTsub_pointer(t1,t2) ->
	JCTsub_pointer(map_term f t1,map_term f t2)
    | JCTderef(t1,fi) ->
	JCTderef(map_term f t1,fi)
    | JCTapp app ->
	let tl = app.jc_app_args in
	JCTapp { app with jc_app_args = List.map (map_term f) tl; }
    | JCTold t ->
	JCTold(map_term f t)
    | JCToffset(off,t,st) ->
	JCToffset(off,map_term f t,st)
    | JCTinstanceof(t,st) ->
	JCTinstanceof(map_term f t,st)
    | JCTcast(t,st) ->
	JCTcast(map_term f t,st)
    | JCTif(t1,t2,t3) ->
	JCTif(map_term f t1,map_term f t2,map_term f t3)
    | JCTrange(Some t1,Some t2) ->
	JCTrange(Some (map_term f t1),Some (map_term f t2))
    | JCTrange(Some t1,None) ->
	JCTrange(Some (map_term f t1),None)
    | JCTrange(None,Some t2) ->
	JCTrange(None,Some (map_term f t2))
  in
  f { t with jc_term_node = tnode; }


(*****************************************************************************)
(* Specific iterators on terms.                                              *)
(*****************************************************************************)

let raw_sub_term subt t =
  fold_term (fun acc t -> acc || raw_term_equal subt t) false t

let raw_strict_sub_term subt t =
  raw_term_compare subt t <> 0 && raw_sub_term subt t


(*****************************************************************************)
(* General iterators on assertions.                                          *)
(*****************************************************************************)

let rec iter_term_and_assertion ft fa a =
  fa a;
  match a.jc_assertion_node with
    | JCAtrue | JCAfalse | JCAtagequality _ -> ()
    | JCArelation(t1,_,t2) -> 
	iter_term ft t1;
	iter_term ft t2
    | JCAapp(_,tls) ->
	List.iter (iter_term ft) tls
    | JCAinstanceof(t1,_) | JCAbool_term t1 | JCAmutable(t1,_,_) ->
	iter_term ft t1
    | JCAand al | JCAor al ->
	List.iter (iter_term_and_assertion ft fa) al
    | JCAimplies(a1,a2) | JCAiff(a1,a2) ->
	iter_term_and_assertion ft fa a1;
	iter_term_and_assertion ft fa a2
    | JCAif(t1,a1,a2) ->
	iter_term ft t1;
	iter_term_and_assertion ft fa a1;
	iter_term_and_assertion ft fa a2
    | JCAnot a1 | JCAquantifier(_,_,a1) | JCAold a1 ->
	iter_term_and_assertion ft fa a1

let iter_term_and_assertion_in_loop_annot ft fa la =
  iter_term_and_assertion ft fa la.jc_loop_invariant;
  Option_misc.iter (iter_term ft) la.jc_loop_variant

let iter_term_and_assertion_in_behavior ft fa bv =
  Option_misc.iter (iter_term_and_assertion ft fa) bv.jc_behavior_assumes;
  (* TODO: assigns *)
  iter_term_and_assertion ft fa bv.jc_behavior_ensures

let iter_term_and_assertion_in_fun_spec ft fa spec =
  iter_term_and_assertion ft fa spec.jc_fun_requires;
  List.iter (fun (_,_,bv) -> iter_term_and_assertion_in_behavior ft fa bv)
    spec.jc_fun_behavior

let rec fold_assertion f acc a =
  let acc = f acc a in
  match a.jc_assertion_node with
    | JCAtrue | JCAfalse | JCArelation _ | JCAapp _ | JCAtagequality _ 
    | JCAinstanceof _ | JCAbool_term _ | JCAmutable _ -> 
	acc
    | JCAand al | JCAor al ->
	List.fold_left (fold_assertion f) acc al
    | JCAimplies(a1,a2) | JCAiff(a1,a2) | JCAif(_,a1,a2) ->
	let acc = fold_assertion f acc a1 in
	fold_assertion f acc a2
    | JCAnot a1 | JCAquantifier(_,_,a1) | JCAold a1 ->
	fold_assertion f acc a1

let rec fold_term_in_assertion f acc a =
  match a.jc_assertion_node with
    | JCAtrue | JCAfalse | JCAtagequality _ -> acc
    | JCArelation(t1,_,t2) -> 
	let acc = fold_term f acc t1 in
	fold_term f acc t2
    | JCAapp(_,tls) ->
	List.fold_left (fold_term f) acc tls
    | JCAinstanceof(t1,_) | JCAbool_term t1 | JCAmutable(t1,_,_) ->
	fold_term f acc t1
    | JCAand al | JCAor al ->
	List.fold_left (fold_term_in_assertion f) acc al
    | JCAimplies(a1,a2) | JCAiff(a1,a2) ->
	let acc = fold_term_in_assertion f acc a1 in
	fold_term_in_assertion f acc a2
    | JCAif(t1,a1,a2) ->
	let acc = fold_term f acc t1 in
	let acc = fold_term_in_assertion f acc a1 in
	fold_term_in_assertion f acc a2
    | JCAnot a1 | JCAquantifier(_,_,a1) | JCAold a1 ->
	fold_term_in_assertion f acc a1

let rec fold_term_and_assertion ft fa acc a =
  let acc = match a.jc_assertion_node with
    | JCAtrue | JCAfalse | JCAtagequality _ -> acc
    | JCArelation(t1,_,t2) -> 
	let acc = fold_term ft acc t1 in
	fold_term ft acc t2
    | JCAapp(_,tls) ->
	List.fold_left (fold_term ft) acc tls
    | JCAinstanceof(t1,_) | JCAbool_term t1 | JCAmutable(t1,_,_) ->
	fold_term ft acc t1
    | JCAand al | JCAor al ->
	List.fold_left (fold_term_and_assertion ft fa) acc al
    | JCAimplies(a1,a2) | JCAiff(a1,a2) ->
	let acc = fold_term_and_assertion ft fa acc a1 in
	fold_term_and_assertion ft fa acc a2
    | JCAif(t1,a1,a2) ->
	let acc = fold_term ft acc t1 in
	let acc = fold_term_and_assertion ft fa acc a1 in
	fold_term_and_assertion ft fa acc a2
    | JCAnot a1 | JCAquantifier(_,_,a1) | JCAold a1 ->
	fold_term_and_assertion ft fa acc a1
  in
  fa acc a

let rec map_assertion f a =
  let anode = match a.jc_assertion_node with
    | JCAtrue | JCAfalse | JCArelation _ | JCAapp _ | JCAtagequality _ 
    | JCAinstanceof _ | JCAbool_term _ | JCAmutable _ as anode -> 
	anode
    | JCAand al ->
	JCAand(List.map (map_assertion f) al)
    | JCAor al ->
	JCAor(List.map (map_assertion f) al)
    | JCAimplies(a1,a2) ->
	JCAimplies(map_assertion f a1,map_assertion f a2)
    | JCAiff(a1,a2) ->
	JCAiff(map_assertion f a1,map_assertion f a2)
    | JCAif(t,a1,a2) ->
	JCAif(t,map_assertion f a1,map_assertion f a2)
    | JCAnot a1 ->
	JCAnot(map_assertion f a1)
    | JCAquantifier(q,vi,a1) ->
	JCAquantifier(q,vi,map_assertion f a1)
    | JCAold a1 ->
	JCAold(map_assertion f a1)
  in
  f { a with jc_assertion_node = anode; }

let rec map_term_in_assertion f a =
  let anode = match a.jc_assertion_node with
    | JCAtrue | JCAfalse | JCAtagequality _ as anode -> anode
    | JCArelation(t1,op,t2) -> 
	JCArelation(map_term f t1,op,map_term f t2)
    | JCAapp(li,tls) ->
	JCAapp(li,List.map (map_term f) tls)
    | JCAinstanceof(t1,st) ->
	JCAinstanceof(map_term f t1,st)
    | JCAbool_term t1 ->
	JCAbool_term(map_term f t1)
    | JCAmutable(t1,st,tag) ->
	JCAmutable(map_term f t1,st,tag)
    | JCAand al ->
	JCAand(List.map (map_term_in_assertion f) al)
    | JCAor al ->
	JCAor(List.map (map_term_in_assertion f) al)
    | JCAimplies(a1,a2) ->
	JCAimplies
	  (map_term_in_assertion f a1,map_term_in_assertion f a2)
    | JCAiff(a1,a2) ->
	JCAiff
	  (map_term_in_assertion f a1,map_term_in_assertion f a2)
    | JCAif(t1,a1,a2) ->
	JCAif(
	  map_term f t1,
	  map_term_in_assertion f a1,
	  map_term_in_assertion f a2)
    | JCAnot a1 ->
	JCAnot(map_term_in_assertion f a1)
    | JCAquantifier(q,vi,a1) ->
	JCAquantifier(q,vi,map_term_in_assertion f a1)
    | JCAold a1 ->
	JCAold(map_term_in_assertion f a1)
  in
  { a with jc_assertion_node = anode; }

let rec map_term_in_assertion f a =
  let anode = match a.jc_assertion_node with
    | JCAtrue | JCAfalse | JCAtagequality _ as anode -> anode
    | JCArelation(t1,op,t2) -> 
	JCArelation(map_term f t1,op,map_term f t2)
    | JCAapp(li,tls) ->
	JCAapp(li,List.map (map_term f) tls)
    | JCAinstanceof(t1,st) ->
	JCAinstanceof(map_term f t1,st)
    | JCAbool_term t1 ->
	JCAbool_term(map_term f t1)
    | JCAmutable(t1,st,tag) ->
	JCAmutable(map_term f t1,st,tag)
    | JCAand al ->
	JCAand(List.map (map_term_in_assertion f) al)
    | JCAor al ->
	JCAor(List.map (map_term_in_assertion f) al)
    | JCAimplies(a1,a2) ->
	JCAimplies
	  (map_term_in_assertion f a1,map_term_in_assertion f a2)
    | JCAiff(a1,a2) ->
	JCAiff
	  (map_term_in_assertion f a1,map_term_in_assertion f a2)
    | JCAif(t1,a1,a2) ->
	JCAif(
	  map_term f t1,
	  map_term_in_assertion f a1,
	  map_term_in_assertion f a2)
    | JCAnot a1 ->
	JCAnot(map_term_in_assertion f a1)
    | JCAquantifier(q,vi,a1) ->
	JCAquantifier(q,vi,map_term_in_assertion f a1)
    | JCAold a1 ->
	JCAold(map_term_in_assertion f a1)
  in
  { a with jc_assertion_node = anode; }


(*
Local Variables: 
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*)
