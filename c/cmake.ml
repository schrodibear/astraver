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

(*i $Id: cmake.ml,v 1.2 2004-11-11 03:02:11 filliatr Exp $ i*)

open Format
open Pp

let files = Hashtbl.create 97

let add ~file ~f =
  let l = try Hashtbl.find files file with Not_found -> [] in
  Hashtbl.replace files file (f :: l)

let simplify fmt file f = fprintf fmt "simplify/%s__%s_why.sx" file f
let simplify_all fmt file f = fprintf fmt "simplify/%s__%s_why.sx.all" file f
let coq_v fmt file f = fprintf fmt "coq/%s__%s_why.v" file f
let coq_vo fmt file f = fprintf fmt "coq/%s__%s_why.vo" file f
let pvs fmt file f = fprintf fmt "pvs/%s__%s_why.pvs" file f
let cvcl_all fmt file f = fprintf fmt "cvcl/%s__%s_why.cvc.all" file f

let print_files file p = 
  print_list (fun fmt () -> fprintf fmt "\\@\n  ") (fun fmt f -> p fmt file f)

let generic f targets =
  print_in_file 
    (fun fmt -> 
       fprintf fmt 
       "# this makefile was automatically generated; do not edit @\n@\n";
       fprintf fmt "WHY=why %s@\n@\n" Coptions.why_opt;	    
       fprintf fmt "CADULIB=%s@\n@\n" Coptions.libdir;	    
       fprintf fmt "COQTACTIC=%s@\n@\n" Coptions.coq_tactic;	    
       fprintf fmt ".PHONY: all coq pvs simplify cvcl@\n@\n";
       fprintf fmt "all: coq/caduceus_spec_why.v %a@\n@\n" 
	 (print_files f simplify) targets;
       fprintf fmt "coq: %a@\n@\n" (print_files f coq_vo) targets;
       fprintf fmt "coq/%%_why.v: coq/caduceus_spec_why.v why/caduceus_spec.why why/%%.why@\n";
       fprintf fmt "\t@@echo 'why -coq-v8 [...] why/$*.why' &&$(WHY) -coq-v8 -dir coq -coq-preamble \"Require Export caduceus_spec_why.\" -coq-tactic \"$(COQTACTIC)\" $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/$*.why@\n@\n";
       fprintf fmt "coq/caduceus_spec_why.v: why/caduceus_spec.why@\n";
       fprintf fmt "\t@@echo 'why -coq-v8 [...] why/caduceus_spec.why' && $(WHY) -coq-v8 -dir coq -coq-preamble \"Require Export caduceus_why. Require Export caduceus_tactics.\" $(CADULIB)/why/caduceus.why why/caduceus_spec.why@\n@\n";
       fprintf fmt "coq/%%.vo: coq/%%.v@\n\tcoqc -I coq $<@\n@\n";
       
       fprintf fmt "pvs: %a@\n@\n" (print_files f pvs) targets;
       fprintf fmt "pvs/%%_why.pvs: pvs/caduceus_spec_why.pvs why/%%.why@\n";
       fprintf fmt "\t$(WHY) -pvs -dir pvs -pvs-preamble \"importing caduceus_spec_why\" $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/$*.why@\n@\n";
       fprintf fmt "pvs/caduceus_spec_why.pvs: pvs/caduceus_why.pvs why/caduceus_spec.why@\n";
       fprintf fmt "\t$(WHY) -pvs -dir pvs -pvs-preamble \"importing caduceus_why\" $(CADULIB)/why/caduceus.why why/caduceus_spec.why@\n@\n";
       fprintf fmt "pvs/caduceus_why.pvs:@\n";
       fprintf fmt "\t$(WHY) -pvs -dir pvs $(CADULIB)/why/caduceus.why@\n@\n";
       
       fprintf fmt "simplify: %a@\n" (print_files f simplify_all) targets;
       fprintf fmt "\t@@echo 'Running Simplify on proof obligations' && (dp -timeout 10 $^)@\n@\n";
       fprintf fmt "simplify/%%_why.sx.all: simplify/%%_why.sx@\n";
       fprintf fmt "\t@@cat simplify/caduceus_why.sx simplify/caduceus_spec_why.sx $< > $@@@\n@\n";
       fprintf fmt "simplify/%%_why.sx: why/caduceus_spec.why why/%%.why@\n";
       fprintf fmt "\t@@echo 'why -simplify [...] why/$*.why' && $(WHY) -simplify -no-simplify-prelude -dir simplify $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/$*.why@\n@\n";
       
       fprintf fmt "cvcl: %a@\n@\n" (print_files f cvcl_all) targets;
       fprintf fmt "\t@@echo 'Running CVC Lite on proof obligations' && (dp -timeout 10 $^)@\n@\n";
       fprintf fmt "cvcl/%%_why.cvc.all: cvcl/%%_why.cvc@\n";
       fprintf fmt "\t@@cat cvcl/caduceus_why.cvc cvcl/caduceus_spec_why.cvc $< > $@@@\n@\n";
       fprintf fmt "cvcl/%%_why.cvc: why/caduceus_spec.why why/%%.why@\n";
       fprintf fmt "\t@@echo 'why -cvcl [...] why/$*.why' && $(WHY) -cvcl -no-cvcl-prelude -dir cvcl $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/$*.why@\n@\n";
       
       fprintf fmt "include %s.depend@\n@\n" f;
       fprintf fmt "depend %s.depend: coq/caduceus_spec_why.v coq/caduceus_tactics.v %a@\n" f (print_files f coq_v) targets;
       fprintf fmt "\t-coqdep -I coq coq/*.v > %s.depend@\n@\n" f;
       fprintf fmt "clean:@\n";
       fprintf fmt "\trm -f coq/*.vo@\n@\n";
    )
    (f ^ ".makefile")

let makefile f =
  let f = Filename.chop_extension f in
  if Coptions.separate then
    let l = try Hashtbl.find files f with Not_found -> [] in
    generic f l
  else
    generic f [f]



