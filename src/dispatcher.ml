(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: dispatcher.ml,v 1.1 2005-06-22 06:53:57 filliatr Exp $ i*)

open Vcg
open Logic

type elem =
  | Logic of string * logic_type Env.scheme
  | Axiom of string * predicate Env.scheme
  | PredicateDef of string * predicate_def Env.scheme
  | FunctionDef of string * function_def Env.scheme

let stack = ref []

let add_elem e = stack := e :: !stack

let push_logic id t = add_elem (Logic (id,t))

let push_axiom id p = add_elem (Axiom (id, p))

let push_predicate id p = add_elem (PredicateDef (id, p))

let push_function id p = add_elem (FunctionDef (id, p))

let oblig = Queue.create ()
let oblig_h = Hashtbl.create 97

let add_oblig ((_,id,_) as o) =
  let so = (!stack, o) in
  Queue.add so oblig;
  Hashtbl.add oblig_h id so

let push_obligations = List.iter add_oblig

let iter f = Queue.iter (fun (_,o) -> f o) oblig

(* calling prover *)

type prover = Simplify | Harvey

let push_elem p e = match p, e with
  | Simplify, Logic _ -> ()
  | Simplify, Axiom (id, a) -> Simplify.push_axiom id a
  | Simplify, PredicateDef (id, p) -> Simplify.push_predicate id p
  | Simplify, FunctionDef (id, f) -> Simplify.push_function id f
  | _ -> assert false (*TODO*)

let push_obligation p o = match p with
  | Simplify -> Simplify.push_obligations [o]
  | Harvey -> Harvey.push_obligations [o]

let output_file p (elems,o) =
  List.iter (push_elem p) elems;
  push_obligation p o;
  let f = Filename.temp_file "gwhy" "" in
  match p with
    | Simplify -> Simplify.output_file f; f ^ "_why.sx"
    | Harvey -> Harvey.output_file f; f ^ "_why.rv"

let call_prover ~obligation:o p =
  let so = try Hashtbl.find oblig_h o with Not_found -> assert false in
  let filename = output_file p so in
  let r = match p with
    | Simplify -> 
	Calldp.simplify ~filename () 
    | Harvey -> 
	(match Calldp.harvey ~filename () with [r] -> r | _ -> assert false)
  in
  Sys.remove filename;
  r

