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

(*i $Id: cmake.ml,v 1.1 2004-11-08 16:10:01 filliatr Exp $ i*)

open Format

let files = Hashtbl.create 97

let add ~file ~f =
  let l = try Hashtbl.find files file with Not_found -> [] in
  Hashtbl.replace files file (f :: l)

let makefile f =
  let f = Filename.chop_extension f in
  Pp.print_in_file 
    (fun fmt -> 
       fprintf fmt 
	 "# this makefile was automatically generated; do not edit @\n@\n";
       fprintf fmt "WHY=why %s@\n@\n" Coptions.why_opt;	    
       fprintf fmt "CADULIB=%s@\n@\n" Coptions.libdir;	    
       fprintf fmt "COQTACTIC=%s@\n@\n" Coptions.coq_tactic;	    
       fprintf fmt ".PHONY: all coq pvs simplify cvcl@\n@\n";
       fprintf fmt "all: coq/caduceus_spec_why.v simplify/%s_why.sx@\n@\n" f;
       
       fprintf fmt "coq: coq/%s_why.vo@\n@\n" f;
       fprintf fmt "coq/%s_why.v: why/caduceus_spec.why coq/caduceus_spec_why.v why/%s.why@\n" f f;
       fprintf fmt "\t@@echo 'why -coq-v8 [...] why/%s.why' &&$(WHY) -coq-v8 -dir coq -coq-preamble \"Require Export caduceus_spec_why.\" -coq-tactic \"$(COQTACTIC)\" $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/%s.why@\n@\n" f f;
       fprintf fmt "coq/caduceus_spec_why.v: why/caduceus_spec.why@\n";
       fprintf fmt "\t@@echo 'why -coq-v8 [...] why/caduceus_spec.why' && $(WHY) -coq-v8 -dir coq -coq-preamble \"Require Export caduceus_why. Require Export caduceus_tactics.\" $(CADULIB)/why/caduceus.why why/caduceus_spec.why@\n@\n";
       fprintf fmt "coq/%%.vo: coq/%%.v@\n\tcoqc -I coq $<@\n@\n";
       
       fprintf fmt "pvs: pvs/%s_why.pvs@\n@\n" f;
       fprintf fmt "pvs/%s_why.pvs: pvs/caduceus_spec_why.pvs why/%s.why@\n" f f;
       fprintf fmt "\t$(WHY) -pvs -dir pvs -pvs-preamble \"importing caduceus_spec_why\" $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/%s.why@\n@\n" f;
       fprintf fmt "pvs/caduceus_spec_why.pvs: pvs/caduceus_why.pvs why/caduceus_spec.why@\n";
       fprintf fmt "\t$(WHY) -pvs -dir pvs -pvs-preamble \"importing caduceus_why\" $(CADULIB)/why/caduceus.why why/caduceus_spec.why@\n@\n";
       fprintf fmt "pvs/caduceus_why.pvs:@\n";
       fprintf fmt "\t$(WHY) -pvs -dir pvs $(CADULIB)/why/caduceus.why@\n@\n";
       
       fprintf fmt "simplify: simplify/%s_why.sx.all@\n" f;
       fprintf fmt "\t@@echo 'Running Simplify on proof obligations for %s.c' && (dp -timeout 10 $<)@\n@\n" f;
       fprintf fmt "simplify/%s_why.sx.all: simplify/%s_why.sx@\n" f f;
       fprintf fmt "\t@@cat simplify/caduceus_why.sx simplify/caduceus_spec_why.sx $< > $@@@\n@\n";
       fprintf fmt "simplify/%s_why.sx: why/caduceus_spec.why why/%s.why@\n" f f;
       fprintf fmt "\t@@echo 'why -simplify [...] why/%s.why' && $(WHY) -simplify -no-simplify-prelude -dir simplify $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/%s.why@\n@\n" f f;
       
       fprintf fmt "cvcl: cvcl/%s_why.cvc.all@\n@\n" f;
       fprintf fmt "\t@@echo 'Running CVC Lite on proof obligations for %s.c' && (dp -timeout 10 $<)@\n@\n" f;
       fprintf fmt "cvcl/%s_why.cvc.all: cvcl/%s_why.cvc@\n" f f;
       fprintf fmt "\t@@cat cvcl/caduceus_why.cvc cvcl/caduceus_spec_why.cvc $< > $@@@\n@\n";
       fprintf fmt "cvcl/%s_why.cvc: why/caduceus_spec.why why/%s.why@\n" f f;
       fprintf fmt "\t@@echo 'why -cvcl [...] why/%s.why' && $(WHY) -cvcl -no-cvcl-prelude -dir cvcl $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/%s.why@\n@\n" f f;
       
       fprintf fmt "include %s.depend@\n@\n" f;
       fprintf fmt "depend %s.depend: coq/caduceus_spec_why.v coq/caduceus_tactics.v coq/%s_why.v@\n" f f;
       fprintf fmt "\t-coqdep -I coq coq/*.v > %s.depend@\n@\n" f;
       fprintf fmt "clean:@\n";
       fprintf fmt "\trm -f coq/*.vo@\n@\n";
    )
    (f ^ ".makefile")

