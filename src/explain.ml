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

(* explanations *)

let program_locs = Hashtbl.create 17

(*
let read_in_file f l b e = 
  let ch = open_in f in
  for i = 2 to l do
    ignore (input_line ch)
  done;
  for i = 1 to b do
    ignore (input_char ch)
  done;
  let buf = Buffer.create 17 in
  for i = b to e-1 do
    Buffer.add_char buf (input_char ch)
  done;
  Buffer.contents buf
*)
 
open Format
open Logic
open Logic_decl

  
let raw_loc ?(quote=false) ?(pref="") fmt (f,l,b,e) =
  if quote 
  then
    begin
      fprintf fmt "%sfile = \"%s\" " pref f;
      fprintf fmt "%sline = \"%d\" " pref l;
      fprintf fmt "%sbegin = \"%d\" " pref b;
      fprintf fmt "%send = \"%d\"" pref e
    end
  else
    begin
      fprintf fmt "%sfile = \"%s\"@\n" pref f;
      fprintf fmt "%sline = %d@\n" pref l;
      fprintf fmt "%sbegin = %d@\n" pref b;
      fprintf fmt "%send = %d@\n" pref e
    end
 
let print_formula fmt s =
  if String.length s > 0 then
    fprintf fmt "formula = \"%s\"@\n" s

let string_of_kind k =
  match k with
    | EKOther _ -> "Other"
    | EKAbsurd -> "Absurd"
    | EKAssert -> "Assert"
    | EKCheck -> "Check"
    | EKPre _ -> "Pre" 
    | EKPost -> "Post"
    | EKWfRel -> "WfRel"
    | EKVarDecr -> "VarDecr" 
    | EKLoopInvInit _ -> "LoopInvInit"
    | EKLoopInvPreserv _ -> "LoopInvPreserv"
    | EKLemma -> "Lemma"
	
let print_kind ?(quote=false) fmt (loc,k,lab) =
  (* 
     Option_misc.iter (fun lab ->  fprintf fmt "label = %s@\n" lab) labopt; 
  *)
  if not quote then
    begin
      raw_loc fmt loc;
      match lab with
	| None -> ()
	| Some s ->
            fprintf fmt "source_label = \"%s\"@\n" s
    end;
  match k with
    | EKOther s | EKPre s -> 
	fprintf fmt "kind = \"%s\"@\ntext = \"%s\"" (string_of_kind k) s
    | EKAbsurd | EKAssert | EKCheck | EKPost | EKWfRel | EKVarDecr 
    | EKLemma -> 
	fprintf fmt "kind = \"%s\"" (string_of_kind k)
    | EKLoopInvInit s | EKLoopInvPreserv s -> 
	fprintf fmt "kind = \"%s\"" (string_of_kind k);
	print_formula fmt s
 
let print ?(quote=false) fmt  e = 
  print_kind ~quote fmt (e.vc_loc,e.vc_kind,e.vc_label)

let msg_of_loopinv = function
  | "" -> "loop invariant"
  | s -> "generated loop inv. '" ^ s ^"'"

let msg_of_kind ?name = 
  function
    | EKPre "PointerDeref" -> "pointer dereferencing"
    | EKPre "IndexBounds" -> "check index bounds"
    | EKPre "ArithOverflow" -> "check arithmetic overflow"
    | EKPre "FPOverflow" -> "check FP overflow"
    | EKPre "DivByZero" -> "check division by zero"
    | EKPre "AllocSize" -> "check allocation size"
    | EKPre "UserCall" -> "precondition for user call"
    | EKPre "" -> "precondition"
    | EKPre s -> "unclassified precondition `" ^ s ^ "'"
    | EKOther s -> "unclassified obligation `" ^ s ^ "'"
    | EKAbsurd -> "code unreachable"
    | EKAssert -> "assertion"
    | EKCheck -> "check"
    | EKPost -> "postcondition"
    | EKWfRel -> "relation is well-founded"
    | EKVarDecr -> "variant decreases" 
    | EKLoopInvInit s -> msg_of_loopinv s ^ " initially holds"
    | EKLoopInvPreserv s -> msg_of_loopinv s ^ " preserved"
    | EKLemma -> "lemma" ^ (match name with None -> "" | Some s -> " " ^ s)
