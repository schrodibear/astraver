(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
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

(*i $Id: dispatcher.ml,v 1.19 2007-02-28 13:58:22 couchot Exp $ i*)

open Options
open Vcg
open Logic
open Logic_decl

type elem = Logic_decl.t

let stack = ref []

let add_elem e = stack := e :: !stack

let oblig = Queue.create ()
let oblig_h = Hashtbl.create 97

let add_oblig ((_,id,_) as o) =
  let so = (List.rev !stack, o) in
  Queue.add so oblig ;
  Hashtbl.add oblig_h id so

let push_decl = function
  | Dgoal (loc, id, s) -> add_oblig (loc, id, s)
  | d -> add_elem d

let iter f = Queue.iter (fun (_,o) -> f o) oblig

(* calling prover *)

type prover = Simplify | Harvey | Cvcl | Zenon | Rvsat | Yices | Ergo

let push_elem p e = 
  if not pruning then 
    assert (match e with Dgoal _ -> false | _ -> true);  
  match p with
  | Simplify -> Simplify.push_decl e
  | Harvey -> Harvey.push_decl e
  | Cvcl -> Cvcl.push_decl e
  | Zenon -> Zenon.push_decl e
  | Rvsat -> Smtlib.push_decl e
  | Yices -> Smtlib.push_decl e
  | Ergo -> Pretty.push_decl e


let push_obligation p (loc, id, s) = 
  let g = Dgoal (loc, id, s) in
  match p with
  | Simplify -> Simplify.push_decl g
  | Harvey -> Harvey.push_decl g
  | Cvcl -> Cvcl.push_decl g
  | Zenon -> Zenon.push_decl g
  | Rvsat -> Smtlib.push_decl g
  | Yices -> Smtlib.push_decl g
  | Ergo -> Pretty.push_decl g

(* output_file is a CRITICAL SECTION *)
(** @parama elems is the List that stores the theory
    @parama o is the proof obligation
**)

let output_file ?encoding p (elems,o) =
  begin match encoding with 
      Some e -> set_types_encoding e 
    | None -> () end;
  begin match p with
    | Simplify -> Simplify.reset () 
    | Harvey -> Harvey.reset () 
    | Cvcl -> Cvcl.prelude_done := false; Cvcl.reset ()
    | Zenon -> Zenon.prelude_done := false; Zenon.reset ()
    | Rvsat -> Smtlib.reset ()
    | Yices -> Smtlib.reset ()
    | Ergo -> Pretty.reset ()
  end;
  if pruning then 
    begin  
      (**stores into the declarationQueue 
	 all the elements of the elems list and th obligation**)  
      let declQ = Queue.create () in
      List.iter (fun p -> Queue.add p declQ) elems ;
      let (loc, id, s) = o in
      let g = Dgoal (loc, id, s) in
      Queue.add g declQ;
      if debug then
	Format.printf "Before the pruning dedicated to the PO: %d @." 
	  (Queue.length declQ);
      (** reduce the theory **)
      let q = Theory_filtering.reduce declQ in 
      if debug then
	Format.printf "After the pruning dedicated to the PO: %d @." 
	  (Queue.length q);
      Queue.iter (push_elem p) q ;
      push_obligation p o 
    end
  else
    begin
      List.iter (push_elem p) elems;
      push_obligation p o
    end;
  let f = Filename.temp_file "gwhy" "" in
  match p with
    | Simplify -> Simplify.output_file f; f ^ "_why.sx"
    | Harvey -> Harvey.output_file f; f ^ "_why.rv"
    | Cvcl -> Cvcl.output_file f; f ^ "_why.cvc"
    | Zenon -> Zenon.output_file f; f ^ "_why.znn"
    | Rvsat -> Smtlib.output_file f; f ^ "_why.smt"
    | Yices -> Smtlib.output_file f; f ^ "_why.smt"
    | Ergo -> Pretty.output_file f; f ^ "_why.why"

open Format

let prover_name = function 
  | Simplify -> "Simplify" 
  | Harvey -> "haRVey"
  | Cvcl -> "CVC Lite"
  | Zenon -> "Zenon"
  | Rvsat -> "rv-sat"
  | Yices -> "Yices"
  | Ergo -> "ergo"

let call_prover ?(debug=false) ?timeout ?encoding ~obligation:o p =
  let so = try Hashtbl.find oblig_h o with Not_found -> assert false in
  let filename = output_file ?encoding p so in
  if debug then eprintf "calling %s on %s@." (prover_name p) filename;
  let r = match p with
    | Simplify -> 
	Calldp.simplify ~debug ?timeout ~filename () 
    | Harvey -> 
	Calldp.harvey ~debug ?timeout ~filename ()
    | Cvcl ->
	Calldp.cvcl ~debug ?timeout ~filename ()
    | Zenon -> 
	Calldp.zenon ~debug ?timeout ~filename ()
    | Rvsat -> 
	Calldp.rvsat ~debug ?timeout ~filename ()
    | Yices -> 
	Calldp.yices ~debug ?timeout ~filename ()
    | Ergo ->
	Calldp.ergo ~debug ?timeout ~filename ()
  in
  if not debug then begin try Sys.remove filename with _ -> () end;
  r

