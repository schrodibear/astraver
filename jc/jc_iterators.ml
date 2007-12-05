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

let rec fold_statement fpre fpost acc s =
  let acc = fpre acc s in
  let acc = match s.jc_statement_node with
    | JCSdecl(_,_,s) | JCScall(_,_,_,s) -> 
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
    | JCScall(_,_,els,s) -> 
	let acc = List.fold_left (fold_expr f) acc els in
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
  | JCTapp(_,tl) ->
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
  | JCTapp(_,tl) ->
      List.fold_left (fold_term f) acc tl
  | JCTif(t1,t2,t3) ->
      let acc = fold_term f acc t1 in
      let acc = fold_term f acc t2 in
      fold_term f acc t3

let rec post_map_term f t =
  let tnode = match t.jc_term_node with
    | JCTconst _ | JCTvar _ | JCTrange (None, None) as tnode -> tnode
    | JCTbinary(t1,bop,t2) ->
	JCTbinary(post_map_term f t1,bop,post_map_term f t2) 
    | JCTunary(uop,t1) ->
	JCTunary(uop,post_map_term f t1)
    | JCTshift(t1,t2) ->
	JCTshift(post_map_term f t1,post_map_term f t2)
    | JCTsub_pointer(t1,t2) ->
	JCTsub_pointer(post_map_term f t1,post_map_term f t2)
    | JCTderef(t1,fi) ->
	JCTderef(post_map_term f t1,fi)
    | JCTapp(li,tl) ->
	JCTapp(li,List.map (post_map_term f) tl)
    | JCTold t ->
	JCTold(post_map_term f t)
    | JCToffset(off,t,st) ->
	JCToffset(off,post_map_term f t,st)
    | JCTinstanceof(t,st) ->
	JCTinstanceof(post_map_term f t,st)
    | JCTcast(t,st) ->
	JCTcast(post_map_term f t,st)
    | JCTif(t1,t2,t3) ->
	JCTif(post_map_term f t1,post_map_term f t2,post_map_term f t3)
    | JCTrange(Some t1,Some t2) ->
	JCTrange(Some (post_map_term f t1),Some (post_map_term f t2))
    | JCTrange(Some t1,None) ->
	JCTrange(Some (post_map_term f t1),None)
    | JCTrange(None,Some t2) ->
	JCTrange(None,Some (post_map_term f t2))
  in
  f { t with jc_term_node = tnode; }

let rec pre_map_term f t =
  let tnode = match f t with
    | Some tnode -> tnode
    | None -> match t.jc_term_node with
      | JCTconst _ | JCTvar _ | JCTrange(None,None) as tnode -> tnode
      | JCTbinary(t1,bop,t2) ->
	  JCTbinary(pre_map_term f t1,bop,pre_map_term f t2) 
      | JCTunary(uop,t1) ->
	  JCTunary(uop,pre_map_term f t1)
      | JCTshift(t1,t2) ->
	  JCTshift(pre_map_term f t1,pre_map_term f t2)
      | JCTsub_pointer(t1,t2) ->
	  JCTsub_pointer(pre_map_term f t1,pre_map_term f t2)
      | JCTderef(t1,fi) ->
	  JCTderef(pre_map_term f t1,fi)
      | JCTapp(li,tl) ->
	  JCTapp(li,List.map (pre_map_term f) tl)
      | JCTold t ->
	  JCTold(pre_map_term f t)
      | JCToffset(off,t,st) ->
	  JCToffset(off,pre_map_term f t,st)
      | JCTinstanceof(t,st) ->
	  JCTinstanceof(pre_map_term f t,st)
      | JCTcast(t,st) ->
	  JCTcast(pre_map_term f t,st)
      | JCTif(t1,t2,t3) ->
	  JCTif(pre_map_term f t1,pre_map_term f t2,pre_map_term f t3)
      | JCTrange(Some t1,Some t2) ->
	  JCTrange(Some (pre_map_term f t1),Some (pre_map_term f t2))
      | JCTrange(Some t1,None) ->
	  JCTrange(Some (pre_map_term f t1),None)
      | JCTrange(None,Some t2) ->
	  JCTrange(None,Some (pre_map_term f t2))
  in
  { t with jc_term_node = tnode; }


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

let rec post_map_term_in_assertion f a =
  let anode = match a.jc_assertion_node with
    | JCAtrue | JCAfalse | JCAtagequality _ as anode -> anode
    | JCArelation(t1,op,t2) -> 
	JCArelation(post_map_term f t1,op,post_map_term f t2)
    | JCAapp(li,tls) ->
	JCAapp(li,List.map (post_map_term f) tls)
    | JCAinstanceof(t1,st) ->
	JCAinstanceof(post_map_term f t1,st)
    | JCAbool_term t1 ->
	JCAbool_term(post_map_term f t1)
    | JCAmutable(t1,st,tag) ->
	JCAmutable(post_map_term f t1,st,tag)
    | JCAand al ->
	JCAand(List.map (post_map_term_in_assertion f) al)
    | JCAor al ->
	JCAor(List.map (post_map_term_in_assertion f) al)
    | JCAimplies(a1,a2) ->
	JCAimplies
	  (post_map_term_in_assertion f a1,post_map_term_in_assertion f a2)
    | JCAiff(a1,a2) ->
	JCAiff
	  (post_map_term_in_assertion f a1,post_map_term_in_assertion f a2)
    | JCAif(t1,a1,a2) ->
	JCAif(
	  post_map_term f t1,
	  post_map_term_in_assertion f a1,
	  post_map_term_in_assertion f a2)
    | JCAnot a1 ->
	JCAnot(post_map_term_in_assertion f a1)
    | JCAquantifier(q,vi,a1) ->
	JCAquantifier(q,vi,post_map_term_in_assertion f a1)
    | JCAold a1 ->
	JCAold(post_map_term_in_assertion f a1)
  in
  { a with jc_assertion_node = anode; }

let rec post_map_assertion f a =
  let anode = match a.jc_assertion_node with
    | JCAtrue | JCAfalse | JCArelation _ | JCAapp _ | JCAtagequality _ 
    | JCAinstanceof _ | JCAbool_term _ | JCAmutable _ as anode -> 
	anode
    | JCAand al ->
	JCAand(List.map (post_map_assertion f) al)
    | JCAor al ->
	JCAor(List.map (post_map_assertion f) al)
    | JCAimplies(a1,a2) ->
	JCAimplies(post_map_assertion f a1,post_map_assertion f a2)
    | JCAiff(a1,a2) ->
	JCAiff(post_map_assertion f a1,post_map_assertion f a2)
    | JCAif(t,a1,a2) ->
	JCAif(t,post_map_assertion f a1,post_map_assertion f a2)
    | JCAnot a1 ->
	JCAnot(post_map_assertion f a1)
    | JCAquantifier(q,vi,a1) ->
	JCAquantifier(q,vi,post_map_assertion f a1)
    | JCAold a1 ->
	JCAold(post_map_assertion f a1)
  in
  f { a with jc_assertion_node = anode; }

(*
Local Variables: 
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*)
