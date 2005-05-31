(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filli�tre - Claude March�
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

(*i $Id: cmake.ml,v 1.10 2005-05-31 07:55:33 filliatr Exp $ i*)

open Format
open Pp

let files = Hashtbl.create 97

let add ~file ~f =
  let l = try Hashtbl.find files file with Not_found -> [] in
  Hashtbl.replace files file (f :: l)

let simplify fmt f = fprintf fmt "simplify/%s_why.sx" f
let simplify_all fmt f = fprintf fmt "simplify/%s_why.sx.all" f
let coq_v fmt f = fprintf fmt "coq/%s_why.v" f
let coq_v_spec fmt f = fprintf fmt "coq/%s_spec_why.v" f
let coq_vo fmt f = fprintf fmt "coq/%s_why.vo" f
let pvs fmt f = fprintf fmt "pvs/%s_why.pvs" f
let cvcl_all fmt f = fprintf fmt "cvcl/%s_why.cvc.all" f
let harvey_all fmt f = fprintf fmt "harvey/%s_why.all.rv" f
let smtlib_all fmt f = fprintf fmt "smtlib/%s_why.smt" f
let isabelle fmt f = fprintf fmt "isabelle/%s_why.thy" f

let print_files = print_list (fun fmt () -> fprintf fmt "\\@\n  ")

let generic f targets =
  print_in_file 
    (fun fmt -> 
       fprintf fmt 
       "# this makefile was automatically generated; do not edit @\n@\n";
       fprintf fmt "WHY=why %s@\n@\n" Coptions.why_opt;	    
       fprintf fmt "CADULIB=%s@\n@\n" Coptions.libdir;	    
       fprintf fmt "COQTACTIC=%s@\n@\n" Coptions.coq_tactic;	    
       fprintf fmt ".PHONY: all coq pvs simplify cvcl harvey smtlib@\n@\n";
       fprintf fmt "all: %a@\n@\n" 
	 (print_files simplify) targets;
       fprintf fmt "coq: %a@\n@\n" (print_files coq_vo) targets;
       fprintf fmt "coq/%%_why.v: why/%%_spec.why why/%%.why@\n";
       fprintf fmt "\t@@echo 'why -coq-v8 [...] why/$*.why' &&$(WHY) -coq-v8 -dir coq -coq-preamble \"Require Export $*_spec_why.\" -coq-tactic \"$(COQTACTIC)\" $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why@\n@\n";
       fprintf fmt "coq/%%_spec_why.v: why/%%_spec.why@\n";
       fprintf fmt "\t@@echo 'why -coq-v8 [...] why/$*_spec.why' && $(WHY) -coq-v8 -dir coq -coq-preamble \"Require Export Caduceus.\" $(CADULIB)/why/caduceus.why why/$*_spec.why@\n@\n";
       fprintf fmt "coq/%%.vo: coq/%%.v@\n\tcoqc -I coq $<@\n@\n";
       
       fprintf fmt "pvs: %a@\n@\n" (print_files pvs) targets;
       fprintf fmt "pvs/%%_why.pvs: pvs/%%_spec_why.pvs why/%%.why@\n";
       fprintf fmt "\t$(WHY) -pvs -dir pvs -pvs-preamble \"importing $*_spec_why\" $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why@\n@\n";
       fprintf fmt "pvs/%%_spec_why.pvs: why/%%_spec.why@\n";
       fprintf fmt "\t$(WHY) -pvs -dir pvs -pvs-preamble \"importing caduceus_why\" $(CADULIB)/why/caduceus.why why/$*_spec.why@\n@\n";
       fprintf fmt "pvs/caduceus_why.pvs:@\n";
       fprintf fmt "\t$(WHY) -pvs -dir pvs $(CADULIB)/why/caduceus.why@\n@\n";
       
       fprintf fmt "isabelle: %a@\n@\n" (print_files isabelle) targets;
       fprintf fmt "isabelle/%%_why.thy: why/%%_spec.why why/%%.why@\n";
       fprintf fmt "\t$(WHY) -isabelle -dir isabelle $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why@\n@\n";
       fprintf fmt "isabelle/%%_spec_why.thy: why/%%_spec.why@\n";
       fprintf fmt "\t$(WHY) -isabelle -dir isabelle $(CADULIB)/why/caduceus.why why/$*_spec.why@\n@\n";

       fprintf fmt "simplify: %a@\n" (print_files simplify_all) targets;
       fprintf fmt "\t@@echo 'Running Simplify on proof obligations' && (dp -timeout 10 $^)@\n@\n";
       fprintf fmt "simplify/%%_why.sx.all: simplify/%%_why.sx@\n";
       fprintf fmt "\t@@cat simplify/caduceus_why.sx simplify/$*_spec_why.sx $< > $@@@\n@\n";
       fprintf fmt "simplify/%%_why.sx: why/%%_spec.why why/%%.why@\n";
       fprintf fmt "\t@@echo 'why -simplify [...] why/$*.why' && $(WHY) -simplify -no-simplify-prelude -dir simplify $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why@\n@\n";
       
       fprintf fmt "cvcl: %a@\n@\n" (print_files cvcl_all) targets;
       fprintf fmt "\t@@echo 'Running CVC Lite on proof obligations' && (dp -timeout 10 $^)@\n@\n";
       fprintf fmt "cvcl/%%_why.cvc.all: cvcl/%%_why.cvc@\n";
       fprintf fmt "\t@@cat cvcl/caduceus_why.cvc cvcl/$*_spec_why.cvc $< > $@@@\n@\n";
       fprintf fmt "cvcl/%%_why.cvc: why/%%_spec.why why/%%.why@\n";
       fprintf fmt "\t@@echo 'why -cvcl [...] why/$*.why' && $(WHY) -cvcl -no-cvcl-prelude -dir cvcl $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why@\n@\n";
       
       fprintf fmt "harvey: %a@\n" (print_files harvey_all) targets;
       fprintf fmt "\t@@echo 'Running haRVey on proof obligations' && (dp -timeout 10 $^)@\n@\n";
       fprintf fmt "harvey/%%_why.all.rv: harvey/%%_why.rv@\n";
       fprintf fmt "\t@@rv_merge harvey/caduceus_why.rv harvey/$*_spec_why.rv $< > $@@@\n@\n";
       fprintf fmt "harvey/%%_why.rv: why/%%_spec.why why/%%.why@\n";
       fprintf fmt "\t@@echo 'why -harvey [...] why/$*.why' && $(WHY) -harvey -dir harvey $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why@\n@\n";
       
       fprintf fmt "smtlib: %a@\n" (print_files smtlib_all) targets;
       fprintf fmt "@\n";
       fprintf fmt "smtlib/%%_why.smt: why/%%_spec.why why/%%.why@\n";
       fprintf fmt "\t@@echo 'why -smtlib [...] why/$*.why' && $(WHY) -smtlib -dir smtlib $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why@\n@\n";
       
       fprintf fmt "include %s.depend@\n@\n" f;
       fprintf fmt "depend %s.depend: %a %a@\n" f 
	 (print_files coq_v_spec) targets (print_files coq_v) targets;
       fprintf fmt "\t-coqdep -I coq coq/*.v > %s.depend@\n@\n" f;
       fprintf fmt "clean:@\n";
       fprintf fmt "\trm -f coq/*.vo@\n@\n";
    )
    (f ^ ".makefile")

let makefile f =
  let f = Filename.chop_extension f in
  if Coptions.separate then
    let l = try Hashtbl.find files f with Not_found -> [] in
    generic f (List.map (fun x -> f ^ "__" ^ x) l)
  else
    generic f [f]



