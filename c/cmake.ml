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

(*i $Id: cmake.ml,v 1.44 2007-02-15 15:52:41 filliatr Exp $ i*)

open Format
open Pp

let files = Hashtbl.create 97

let add ~file ~f =
  let l = try Hashtbl.find files file with Not_found -> [] in
  Hashtbl.replace files file (f :: l)

let simplify fmt f = fprintf fmt "simplify/%s_why.sx" f
let coq_v fmt f = fprintf fmt "coq/%s_why.v" f
let coq_vo fmt f = fprintf fmt "coq/%s_why.vo" f
let pvs fmt f = fprintf fmt "pvs/%s_why.pvs" f
let cvcl fmt f = fprintf fmt "cvcl/%s_why.cvc" f
let harvey fmt f = fprintf fmt "harvey/%s_why.rv" f
let zenon fmt f = fprintf fmt "zenon/%s_why.znn" f
let smtlib fmt f = fprintf fmt "smtlib/%s_why.smt" f
let why_goals fmt f = fprintf fmt "why/%s_ctx.why" f
let isabelle fmt f = 
  fprintf fmt "isabelle/%s_why.thy isabelle/%s_spec_why.thy" f f

let print_files = print_list (fun fmt () -> fprintf fmt "\\@\n  ")

let generic f targets =
  print_in_file 
    (fun fmt -> 
       fprintf fmt 
       "# this makefile was automatically generated; do not edit @\n@\n";
       fprintf fmt "TIMEOUT ?= 10@\n@\n";
       fprintf fmt "WHY=why --no-arrays %s@\n@\n" 
	 (Coptions.why_opt ());
       fprintf fmt "GWHY=gwhy --no-arrays %s@\n@\n" (Coptions.why_opt ());
       fprintf fmt "CADULIB=%s@\n@\n" Coptions.libdir;	    
       fprintf fmt "CADULIBFILE=%s@\n@\n" Coptions.libfile;
       fprintf fmt "COQTACTIC=%s@\n@\n" Coptions.coq_tactic;	    
       fprintf fmt "COQDEP=coqdep -I `coqc -where`/user-contrib@\n@\n";	    
       fprintf fmt ".PHONY: all coq pvs simplify cvcl harvey smtlib zenon@\n@\n";
       fprintf fmt "all: %a@\n@\n" 
	 (print_files simplify) targets;

       fprintf fmt "coq: %a@\n@\n" (print_files coq_vo) targets;

       fprintf fmt "coq/%%_spec_why.v: why/%%_spec.why@\n";
       fprintf fmt "\t@@echo 'why -coq-v8 [...] why/$*_spec.why' && $(WHY) -coq-v8 -dir coq -coq-preamble \"Require Export Caduceus.\" $(CADULIB)/why/$(CADULIBFILE) why/$*_spec.why@\n@\n";

       fprintf fmt "coq/%%_why.v: why/%s_spec.why why/%%.why@\n" f;
       fprintf fmt "\t@@echo 'why -coq-v8 [...] why/$*.why' &&$(WHY) -coq-v8 -dir coq -coq-preamble \"Require Export %s_spec_why.\" -coq-tactic \"$(COQTACTIC)\" $(CADULIB)/why/$(CADULIBFILE) why/%s_spec.why why/$*.why@\n@\n" f f;

       fprintf fmt "coq/%%.vo: coq/%%.v@\n\tcoqc -I coq $<@\n@\n";
       
       fprintf fmt "pvs: %a@\n@\n" (print_files pvs) targets;

       fprintf fmt "pvs/%%_spec_why.pvs: why/%%_spec.why@\n";
       fprintf fmt "\t$(WHY) -pvs -dir pvs -pvs-preamble \"importing caduceus_why\" $(CADULIB)/why/$(CADULIBFILE) why/$*_spec.why@\n@\n";

       fprintf fmt "pvs/%%_why.pvs: pvs/%s_spec_why.pvs why/%%.why@\n" f;
       fprintf fmt "\t$(WHY) -pvs -dir pvs -pvs-preamble \"importing %s_spec_why\" $(CADULIB)/why/$(CADULIBFILE) why/%s_spec.why why/$*.why@\n@\n" f f;

       fprintf fmt "pvs/caduceus_why.pvs:@\n";
       fprintf fmt "\t$(WHY) -pvs -dir pvs $(CADULIB)/why/$(CADULIBFILE)@\n@\n";
       
       fprintf fmt "isabelle: %a@\n@\n" (print_files isabelle) targets;

       fprintf fmt "isabelle/%%_spec_why.thy: why/%%_spec.why@\n";
       fprintf fmt "\t$(WHY) -isabelle -dir isabelle -isabelle-base-theory caduceus_why $(CADULIB)/why/$(CADULIBFILE) why/$*_spec.why@\n@\n";

       fprintf fmt "isabelle/%%_why.thy: isabelle/%s_spec_why.thy why/%%.why@\n" f;
       fprintf fmt "\t$(WHY) -isabelle -dir isabelle -isabelle-base-theory %s_spec_why $(CADULIB)/why/$(CADULIBFILE) why/%s_spec.why why/$*.why@\n" f f;
       fprintf fmt "\tcp -f %s/isabelle/caduceus_why.thy isabelle/@\n@\n" 
	 Coptions.libdir;

       fprintf fmt "simplify: %a@\n" (print_files simplify) targets;
       fprintf fmt "\t@@echo 'Running Simplify on proof obligations' && (dp -timeout $(TIMEOUT) $^)@\n@\n";
       fprintf fmt "simplify/%%_why.sx: why/%s_spec.why why/%%.why@\n" f;
       fprintf fmt "\t@@echo 'why -simplify [...] why/$*.why' && $(WHY) -simplify -no-simplify-prelude -dir  simplify $(CADULIB)/why/$(CADULIBFILE) why/%s_spec.why why/$*.why@\n@\n" f;
       
       fprintf fmt "goals: %a@\n@\n" (print_files why_goals) targets;
       fprintf fmt "why/%%_ctx.why: why/%s_spec.why why/%%.why@\n" f;
       fprintf fmt "\t@@echo 'why --multi-why [...] why/$*.why' && $(WHY) --multi-why -dir why $(CADULIB)/why/$(CADULIBFILE) why/%s_spec.why why/$*.why@\n@\n" f;
       
       fprintf fmt "cvcl: %a@\n@\n" (print_files cvcl) targets;
       fprintf fmt "\t@@echo 'Running CVC Lite on proof obligations' && (dp -timeout $(TIMEOUT) $^)@\n@\n";
       fprintf fmt "cvcl/%%_why.cvc: why/%s_spec.why why/%%.why@\n" f;
       fprintf fmt "\t@@echo 'why -cvcl [...] why/$*.why' && $(WHY) -cvcl --encoding sstrat -dir cvcl $(CADULIB)/why/$(CADULIBFILE) why/%s_spec.why why/$*.why@\n@\n" f;
       
       fprintf fmt "harvey: %a@\n" (print_files harvey) targets;
       fprintf fmt "\t@@echo 'Running haRVey on proof obligations' && (dp -timeout $(TIMEOUT) $^)@\n@\n";
       fprintf fmt "harvey/%%_why.rv: why/%s_spec.why why/%%.why@\n" f;
       fprintf fmt "\t@@echo 'why -harvey [...] why/$*.why' && $(WHY) -harvey -dir harvey $(CADULIB)/why/$(CADULIBFILE) why/%s_spec.why why/$*.why@\n@\n" f;
       
       fprintf fmt "zenon: %a@\n" (print_files zenon) targets;
       fprintf fmt "\t@@echo 'Running Zenon on proof obligations' && (dp -timeout $(TIMEOUT) $^)@\n@\n";
       fprintf fmt "zenon/%%_why.znn: why/%s_spec.why why/%%.why@\n" f;
       fprintf fmt "\t@@echo 'why -zenon [...] why/$*.why' && $(WHY) -zenon -dir zenon $(CADULIB)/why/$(CADULIBFILE) why/%s_spec.why why/$*.why@\n@\n" f;
       
       fprintf fmt "smtlib: %a@\n" (print_files smtlib) targets;
       fprintf fmt "\t@@echo 'Running Yices on proof obligations' && (dp -timeout $(TIMEOUT) $^)@\n@\n";
       fprintf fmt "smtlib/%%_why.smt: why/%s_spec.why why/%%.why@\n" f;
       fprintf fmt "\t@@echo 'why -smtlib [...] why/$*.why' && $(WHY) -smtlib --encoding sstrat --exp goal   -dir smtlib $(CADULIB)/why/$(CADULIBFILE) why/%s_spec.why why/$*.why@\n@\n" f;
       
       fprintf fmt "gui stat: %s@\n" 
	 (match targets with f::_ -> f^".stat" | [] -> "");
       fprintf fmt "@\n";
       fprintf fmt "%%.stat: why/%s_spec.why why/%%.why@\n" f;
       fprintf fmt "\t@@echo 'gwhy [...] why/$*.why' && $(GWHY) $(CADULIB)/why/$(CADULIBFILE) why/%s_spec.why why/$*.why@\n@\n" f;
       
       fprintf fmt "-include %s.depend@\n@\n" f;
       fprintf fmt "depend: coq/%s_spec_why.v %a@\n" f
	 (print_files coq_v) targets;
       fprintf fmt "\t-$(COQDEP) -I coq coq/%s*_why.v > %s.depend@\n@\n" f f;
       fprintf fmt "clean:@\n";
       fprintf fmt "\trm -f coq/*.vo@\n@\n";
    )
    (f ^ ".makefile")

let makefile f =
  if Coptions.separate then
    let l = try Hashtbl.find files f with Not_found -> [] in
    generic f (List.map (fun x -> f ^ "__" ^ x) l)
  else
    generic f [f]



