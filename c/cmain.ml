(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
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

(*i $Id: cmain.ml,v 1.26 2004-03-24 15:07:46 filliatr Exp $ i*)

open Format
open Coptions
open Cerror
open Creport
open Output

let parse_file f =
  let ppf = Cpp.cpp f in
  let c = open_in ppf in
  let p = Clexer.parse c in
  close_in c;
  f, p

let type_file (f,p) = 
  (f, Ctyping.type_file p)

let interp_file (f,p) =
  let (why_code,why_spec,prover) = Cinterp.interp p in
  let f = Filename.chop_extension f in
  let file = Lib.file "why" (f ^ ".why") in
  Pp.print_in_file (fun fmt -> Output.fprintf_why_decls fmt why_code) file;
  why_spec

let file_copy src dest =
  let cin = open_in src
  and cout = open_out dest
  and buff = String.make 1024 ' ' 
  and n = ref 0 
  in
  while n := input cin buff 0 1024; !n <> 0 do 
    output cout buff 0 !n
  done;
  close_in cin; close_out cout

let file_copy_if_different src dst =
  if not (Sys.file_exists dst) || Digest.file dst <> Digest.file src then
    file_copy src dst

let main () = 
  if not (parse_only || type_only || cpp_dump) then begin
    let theorysrc = Filename.concat Coptions.libdir "why/caduceus.why" in
(*
    let theory = Lib.file "why" "caduceus.why" in
    file_copy_if_different theorysrc theory;
*)
    let coqsrc = Filename.concat Coptions.libdir "coq/caduceus_why.v" in
    let coq = Lib.file "coq" "caduceus_why.v" in
    file_copy_if_different coqsrc coq;
    let coqtactics = Filename.concat Coptions.libdir "coq/caduceus_tactics.v" in
    let coq = Lib.file "coq" "caduceus_tactics.v" in
    file_copy_if_different coqtactics coq
  end;
  (* parsing *)
  let pfiles = List.map parse_file (files ()) in
  if parse_only then exit 0;
  (* typing *)
  let tfiles = List.map type_file pfiles in
  if type_only then exit 0;
  (* effects *)
  List.iter (fun (_,p) -> Ceffect.file p) tfiles;
  while not (List.for_all (fun (_,p) -> Ceffect.functions p) tfiles) do 
    () 
  done;
  lprintf "heap variables: %a@." Ceffect.print_heap_vars ();
  (* Why interpretation *)
  let why_specs =
    List.fold_left (fun specs f -> let s = interp_file f in s @ specs) 
      [] tfiles
  in
  (* Why specs *)
  let file = Lib.file "why" "caduceus_spec.why" in
  Pp.print_in_file 
    (fun fmt -> 
       fprintf fmt 
	 "(* this file was automatically generated; do not edit *)@\n@\n";
       fprintf fmt "(* heap variables *)@\n";
       Hashtbl.iter 
	 (fun v bt -> 
	    let d = Param (false, v, Ref_type (Base_type bt)) in
	    fprintf fmt "@[%a@]" fprintf_why_decls [d])
	 Ceffect.heap_vars;
       fprintf fmt "(* functions specifications *)@\n";
       Output.fprintf_why_decls fmt why_specs) 
    file;
  (* makefile *)
  List.iter 
    (fun f ->
       let f = Filename.chop_extension f in
       Pp.print_in_file 
	 (fun fmt -> 
	    fprintf fmt 
	      "# this makefile was automatically generated; do not edit @\n@\n";
	    fprintf fmt "CADULIB=%s@\n@\n" Coptions.libdir;	    
	    fprintf fmt ".PHONY: all coq simplify@\n@\n";
	    fprintf fmt "all: coq/caduceus_spec_why.v simplify/%s_why.sx@\n@\n" f;

	    fprintf fmt "coq: coq/%s_why.vo@\n@\n" f;
	    fprintf fmt "coq/%s_why.v: why/caduceus_spec.why coq/caduceus_spec_why.v why/%s.why@\n" f f;
	    fprintf fmt "\twhy -coq-v8 -dir coq -coq-preamble \"Require Export caduceus_spec_why.\" -coq-tactic \"intuition\" $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/%s.why@\n@\n" f;
	    fprintf fmt "coq/caduceus_spec_why.v: why/caduceus_spec.why@\n";
	    fprintf fmt "\twhy -coq-v8 -dir coq -coq-preamble \"Require Export caduceus_why. Require Export caduceus_tactics.\" $(CADULIB)/why/caduceus.why why/caduceus_spec.why@\n@\n";
	    fprintf fmt "coq/%%.vo: coq/%%.v@\n\tcoqc -I coq $<@\n@\n";

	    fprintf fmt "simplify:@\n";
	    fprintf fmt "\ttime make -f %s.makefile clean do_simplify > simplify.log@\n" f;
	    fprintf fmt "\t@@echo -n \"valid obligations: \" @\n";
	    fprintf fmt "\t@@egrep '[0-9]+: Valid.$$' simplify.log | wc -l @\n";
	    fprintf fmt "\t@@echo -n \"invalid obligations: \"  @\n";
	    fprintf fmt "\t@@egrep '[0-9]+: Invalid.$$' simplify.log | wc -l @\n\n";
	    fprintf fmt "do_simplify: simplify/%s_why.sxcheck@\n@\n" f;
	    fprintf fmt "simplify/%%.sxcheck: simplify/%%.sx@\n";
	    fprintf fmt "\tcat simplify/caduceus_why.sx simplify/caduceus_spec_why.sx $< > $<.all@\n";
	    fprintf fmt "\tSimplify $<.all@\n@\n";
	    fprintf fmt "simplify/%s_why.sx: why/caduceus_spec.why why/%s.why@\n" f f;
	    fprintf fmt "\twhy -simplify -dir simplify $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/%s.why@\n@\n" f;

	    fprintf fmt "include %s.depend@\n@\n" f;
	    fprintf fmt "depend %s.depend: coq/caduceus_spec_why.v coq/caduceus_tactics.v coq/%s_why.v@\n" f f;
	    fprintf fmt "\t-coqdep -I coq coq/*.v > %s.depend@\n@\n" f;
	    fprintf fmt "clean:@\n";
	    fprintf fmt "\trm -f coq/*.vo coq/caduceus_spec_why.v@\n@\n";
	 )
	 (f ^ ".makefile"))
    (files ())
       
       
 
let rec explain_exception fmt = function
  | Parsing.Parse_error -> 
      fprintf fmt "Syntax error"
  | Stream.Error s -> 
      fprintf fmt "Syntax error: %s" s
  | Error (Some loc, e) | Stdpp.Exc_located (_, Error (Some loc, e)) ->
      fprintf fmt "%a%a" Loc.report loc report e
  | Stdpp.Exc_located (loc, e) ->
      fprintf fmt "%a%a" Loc.report loc explain_exception e
  | Error (_, e) ->
      report fmt e
  | e ->
      fprintf fmt "Anomaly: %s" (Printexc.to_string e)

let () =
  try
    main ()
  with e ->
    eprintf "%a@." explain_exception e;
    exit 1
