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

(*i $Id: dispatcher.ml,v 1.5 2006-03-01 14:52:12 filliatr Exp $ i*)

open Options
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
  let so = (List.rev !stack, o) in
  Queue.add so oblig;
  Hashtbl.add oblig_h id so

let push_obligations = List.iter add_oblig

let iter f = Queue.iter (fun (_,o) -> f o) oblig

(* calling prover *)

type prover = Simplify | Harvey | Cvcl | Zenon

let push_elem p e = match p, e with
  | Simplify, Logic _ -> ()
  | Simplify, Axiom (id, a) -> Simplify.push_axiom id a
  | Simplify, PredicateDef (id, p) -> Simplify.push_predicate id p
  | Simplify, FunctionDef (id, f) -> Simplify.push_function id f
  | Harvey, Logic _ -> ()
  | Harvey, Axiom (id, a) -> Harvey.push_axiom id a
  | Harvey, PredicateDef (id, p) -> Harvey.push_predicate id p
  | Harvey, FunctionDef (id, f) -> Harvey.push_function id f
  | Cvcl, Logic (id, d) -> Cvcl.push_logic id d
  | Cvcl, Axiom (id, a) -> Cvcl.push_axiom id a
  | Cvcl, PredicateDef (id, p) -> Cvcl.push_predicate id p
  | Cvcl, FunctionDef (id, f) -> Cvcl.push_function id f
  | Zenon, Logic (id, d) -> Zenon.push_logic id d
  | Zenon, Axiom (id, a) -> Zenon.push_axiom id a
  | Zenon, PredicateDef (id, p) -> Zenon.push_predicate id p
  | Zenon, FunctionDef (id, f) -> Zenon.push_function id f

let push_obligation p o = match p with
  | Simplify -> Simplify.push_obligations [o]
  | Harvey -> Harvey.push_obligations [o]
  | Cvcl -> Cvcl.push_obligations [o]
  | Zenon -> Zenon.push_obligations [o]

(* output_file is a CRITICAL SECTION *)
let output_file p (elems,o) =
  begin match p with
    | Simplify -> Simplify.reset () 
    | Harvey -> Harvey.reset () 
    | Cvcl -> Cvcl.prelude_done := false; Cvcl.reset ()
    | Zenon -> Zenon.prelude_done := false; Zenon.reset ()
  end;
  List.iter (push_elem p) elems;
  push_obligation p o;
  let f = Filename.temp_file "gwhy" "" in
  match p with
    | Simplify -> Simplify.output_file f; f ^ "_why.sx"
    | Harvey -> Harvey.output_file f; f ^ "_why.rv"
    | Cvcl -> Cvcl.output_file f; f ^ "_why.cvc"
    | Zenon -> Zenon.output_file f; f ^ "_why.znn"

open Printf

let prover_name = function 
  | Simplify -> "Simplify" 
  | Harvey -> "haRVey"
  | Cvcl -> "CVC Lite"
  | Zenon -> "Zenon"

let call_prover ~obligation:o ?timeout p =
  let so = try Hashtbl.find oblig_h o with Not_found -> assert false in
  let filename = output_file p so in
  if debug then begin
    eprintf "calling %s on %s\n" (prover_name p) filename; flush stderr;
  end;
  let r = match p with
    | Simplify -> 
	Calldp.simplify ?timeout ~filename () 
    | Harvey -> 
	(match Calldp.harvey ?timeout ~filename () with 
	   | [r] -> r | _ -> assert false)
    | Cvcl ->
	Calldp.cvcl ?timeout ~filename ()
    | Zenon -> 
	Calldp.zenon ?timeout ~filename ()
  in
  if not debug then begin try Sys.remove filename with _ -> () end;
  r

