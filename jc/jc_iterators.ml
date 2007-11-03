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
  f tnode

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

(*
Local Variables: 
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*)