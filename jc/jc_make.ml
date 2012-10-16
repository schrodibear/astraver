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



open Format
open Pp

(*
let files = Hashtbl.create 97

let add ~file ~f =
  let l = try Hashtbl.find files file with Not_found -> [] in
  Hashtbl.replace files file (f :: l)
*)

let simplify fmt f = fprintf fmt "simplify/%s_why.sx" f
let vampire fmt f = fprintf fmt "vampire/%s_why.vp" f
let coq_v fmt f = fprintf fmt "coq/%s_why.v" f
let coq_vo fmt f = fprintf fmt "coq/%s_why.vo" f
let pvs fmt f = fprintf fmt "pvs/%s_why.pvs" f
let cvcl fmt f = fprintf fmt "cvcl/%s_why.cvc" f
let harvey fmt f = fprintf fmt "harvey/%s_why.rv" f
let zenon fmt f = fprintf fmt "zenon/%s_why.znn" f
let smtlib fmt f = fprintf fmt "smtlib/%s_why.smt" f
let smtlib_v1 fmt f = fprintf fmt "smtlib-v1/%s_why.smt" f
let ergo fmt f = fprintf fmt "why/%s_why.why" f
let gappa fmt f = fprintf fmt "gappa/%s_why.gappa" f
let why_goals fmt f = fprintf fmt "why/%s_ctx.why" f
let wpr fmt f = fprintf fmt "why/%s.wpr" f
let isabelle fmt f = fprintf fmt "isabelle/%s_why.thy" f

let print_files = print_list (fun fmt () -> fprintf fmt "\\@\n  ")

let generic full f targets =
  print_in_file
    (fun fmt ->
       let out x = fprintf fmt x in
       out "# this makefile was automatically generated; do not edit @\n@\n";
       out "TIMEOUT ?= 10@\n@\n";
       out "DP ?= why-dp -timeout $(TIMEOUT)@\n";
       out "WHYEXEC ?= why@\n";
       out "GWHYEXEC ?= gwhy-bin@\n";
       out "WHYLIB ?= %s@\n@\n" (String.escaped Jc_options.libdir);
       out "USERWHYDEUXOPT=%s@\n"  (Jc_options.why_opt);
       out "WHY=WHYLIB=$(WHYLIB) $(WHYEXEC) $(WHYOPT) $(USERWHYDEUXOPT) -explain -locs %s.loc@\n@\n" f;
       out "GWHY=WHYLIB=$(WHYLIB) $(GWHYEXEC) $(WHYOPT) $(USERWHYDEUXOPT) -explain -locs %s.loc@\n@\n"  f;
       out "JESSIELIBFILES ?=";
       List.iter (fun s ->
		    out " %s"
		      (String.escaped (Filename.concat "$(WHYLIB)"
					 (Filename.concat "why" s))))
	 (Jc_options.get_libfiles ());
       out "@\n";
       out "JESSIE3CONF ?= $(WHYLIB)/why3/why3.conf@\n@\n";
       out "COQDEP = coqdep@\n@\n";

       out ".PHONY: all coq pvs simplify vampire cvcl harvey smtlib zenon@\n@\n";
       out "all: %a@\n@\n"
	 (print_files simplify) targets;

       out "project: %a@\n@\n" (print_files wpr) targets;
       out "why/%%.wpr:  WHYOPT=--project -dir why@\n";
       out "why/%%.wpr: why/%%.why@\n";
       out "\t@@echo 'why --project [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       out "goals: %a@\n@\n" (print_files why_goals) targets;
       out "why/%%_ctx.why: WHYOPT=--multi-why -dir why@\n";
       out "why/%%_ctx.why: why/%%.why@\n";
       out "\t@@echo 'why --multi-why [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       out "coq: %a@\n@\n" (print_files coq_vo) targets;

       out "coq/%s_why.v: WHYOPT=-coq -dir coq -coq-preamble \"Require Export jessie_why.\" -coq-tactic \"intuition\"@\n" f;
       out "coq/%s_why.v: why/%s.why@\n" f f;
       out "\t@@echo 'why -coq [...] why/%s.why' && $(WHY) $(JESSIELIBFILES) why/%s.why && rm -f coq/jessie_why.v@\n@\n" f f;

       out "coq-goals: goals coq/%s_ctx_why.vo@\n" f;
       out "\tfor f in why/*_po*.why; do make -f %s.makefile coq/`basename $$f .why`_why.v ; done@\n@\n" f;


       out "coq/%s_ctx_why.v: WHYOPT=-no-pervasives -coq -dir coq -coq-preamble \"Require Export jessie_why.\" -coq-tactic \"intuition\"@\n" f;
       out "coq/%s_ctx_why.v: why/%s_ctx.why@\n" f f;
       out "\t@@echo 'why -coq [...] why/%s_ctx.why' && $(WHY) why/%s_ctx.why@\n@\n" f f;
       out "coq/%%_why.v: WHYOPT=-no-pervasives -coq -dir coq -coq-preamble \"Require Export %s_ctx_why.\" -coq-tactic \"intuition\"@\n" f;
       out "coq/%%_why.v: why/%%.why@\n";
       out "\t@@echo 'why -coq [...] why/$*.why' && $(WHY) why/%s_ctx.why why/$*.why@\n@\n" f;
       out "coq/%%.vo: coq/%%.v@\n\tcoqc -I coq $<@\n";
       out "coq/%%_po_why.vo: coq/%s_ctx_why.vo@\n@\n" f;

       out "pvs: %a@\n@\n" (print_files pvs) targets;

       out "pvs/%%_why.pvs: WHYOPT=-pvs -dir pvs -pvs-preamble \"IMPORTING why@@jessie\"@\n";
       out "pvs/%%_why.pvs: why/%%.why@\n";
       out "\t$(WHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       out "pvs/jessie_why.pvs:WHYOPT=-pvs -dir pvs -pvs-preamble \"IMPORTING why@@why\"@\n";
       out "pvs/jessie_why.pvs:@\n";
       out "\t$(WHY) $(JESSIELIBFILES)@\n@\n";

       out "isabelle: %a@\n@\n" (print_files isabelle) targets;

       out "isabelle/%%_why.thy: WHYOPT=-isabelle -dir isabelle -isabelle-base-theory jessie_why@\n";
       out "isabelle/%%_why.thy: why/%%.why@\n";
       out "\t$(WHY) $(JESSIELIBFILES) why/$*.why@\n";
       out "\tcp -f %s/isabelle/jessie_why.thy isabelle/@\n@\n"
	 Jc_options.libdir;

       out "simplify: %a@\n" (print_files simplify) targets;
       out "\t@@echo 'Running Simplify on proof obligations' && ($(DP) $^)@\n@\n";
       out "simplify/%%_why.sx: WHYOPT=-simplify -dir simplify@\n";
       out "simplify/%%_why.sx: why/%%.why@\n";
       out "\t@@echo 'why -simplify [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       out "vampire: %a@\n" (print_files vampire) targets;
       out "\t@@echo 'Running Vampire on proof obligations' && ($(DP) $^)@\n@\n";
       out "vampire/%%_why.vp: WHYOPT=-vampire -dir vampire@\n";
       out "vampire/%%_why.vp: why/%%.why@\n";
       out "\t@@echo 'why -vampire [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       out "alt-ergo ergo: %a@\n" (print_files ergo) targets;
       out "\t@@echo 'Running Alt-Ergo on proof obligations' && ($(DP) $^)@\n@\n";
       out "why/%%_why.why: WHYOPT=-alt-ergo -dir why@\n";
       out "why/%%_why.why: why/%%.why@\n";
       out "\t@@echo 'why -alt-ergo [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       out "gappa: %a@\n" (print_files gappa) targets;
       out "\t@@echo 'Running Gappa on proof obligations' && ($(DP) $^)@\n@\n";
       out "gappa/%%_why.gappa: WHYOPT=-gappa -dir gappa@\n";
       out "gappa/%%_why.gappa: why/%%.why@\n";
       out "\t@@echo 'why -gappa [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       out "cvcl: %a@\n@\n" (print_files cvcl) targets;
       out "\t@@echo 'Running CVC Lite on proof obligations' && ($(DP) $^)@\n@\n";
       out "cvcl/%%_why.cvc: WHYOPT=-cvcl -dir cvcl@\n";
       out "cvcl/%%_why.cvc: why/%%.why@\n";
       out "\t@@echo 'why -cvcl [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       out "harvey: %a@\n" (print_files harvey) targets;
       out "\t@@echo 'Running haRVey on proof obligations' && ($(DP) $^)@\n@\n";
       out "harvey/%%_why.rv: WHYOPT=-harvey -dir harvey@\n";
       out "harvey/%%_why.rv: why/%%.why@\n";
       out "\t@@echo 'why -harvey [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       out "zenon: %a@\n" (print_files zenon) targets;
       out "\t@@echo 'Running Zenon on proof obligations' && ($(DP) $^)@\n@\n";
       out "zenon/%%_why.znn: WHYOPT=-zenon -dir zenon@\n";
       out "zenon/%%_why.znn: why/%%.why@\n";
       out "\t@@echo 'why -zenon [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       out "smtlib: %a@\n" (print_files smtlib) targets;
       out "\t@@echo 'Running Z3 on proof obligations' && ($(DP) $^)@\n@\n";
       out "smtlib/%%_why.smt:  WHYOPT=-smtlib --encoding sstrat --exp goal -dir smtlib@\n";
       out "smtlib/%%_why.smt: why/%%.why@\n";
       out "\t@@echo 'why -smtlib [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       out "z3: %a@\n" (print_files smtlib) targets;
       out "\t@@echo 'Running Z3 on proof obligations' && ($(DP) -smt-solver z3 $^)@\n@\n";

       out "yices: %a@\n" (print_files smtlib) targets;
       out "\t@@echo 'Running Yices on proof obligations' && ($(DP) -smt-solver yices $^)@\n@\n";

       out "cvc3: %a@\n" (print_files smtlib) targets;
       out "\t@@echo 'Running CVC3 on proof obligations' && ($(DP) -smt-solver cvc3 $^)@\n@\n";

       out "smtlib-v1: %a@\n" (print_files smtlib_v1) targets;
       out "smtlib-v1/%%_why.smt:  WHYOPT=-smtlib --smtlib-v1 --encoding sstrat --exp goal -dir smtlib-v1@\n";
       out "smtlib-v1/%%_why.smt: why/%%.why@\n";
       out "\t@@echo 'why -smtlib [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       out "verit: %a@\n" (print_files smtlib_v1) targets;
       out "\t@@echo 'Running VeriT on proof obligations' && ($(DP) -smt-solver verit $^)@\n@\n";


       out "gui stat: %s@\n"
	 (match targets with f::_ -> f^".stat" | [] -> "");
       out "@\n";
       out "%%.stat: why/%%.why@\n";
       out "\t@@echo 'gwhy-bin [...] why/$*.why' && $(GWHY) $(JESSIELIBFILES) why/$*.why@\n@\n";

       let why3_target =
	 (match targets with f::_ -> f^"_why3.why" | [] -> "")
       in
       out "why3: why/%s@\n" why3_target;

       out "why/%%_why3.why:  WHYOPT=-why3@\n";
       out "why/%%_why3.why: why/%%.why@\n";
       out "\t@@echo 'why -why3 [...] why/$*.why' \
            && $(WHY) $(JESSIELIBFILES) why/$*.why@\n";

       let why3ml_target =
	 (match targets with f::_ -> f^".mlw" | [] -> "")
       in
       out "why3ml: %s@\n" why3ml_target;
       out "\t why3 --extra-config $(JESSIE3CONF) $<@\n@\n";

       out "why3ide: %s@\n" why3ml_target;
       out "\t why3ide --extra-config $(JESSIE3CONF) $<@\n@\n";

       out "why3replay: %s@\n" why3ml_target;
       out "\t why3replayer --extra-config $(JESSIE3CONF) $<@\n@\n";

       out "-include %s.depend@\n@\n" f;
       out "depend: %a@\n" (print_files coq_v) targets;
       out "\t-$(COQDEP) -I coq coq/%s*_why.v > %s.depend@\n@\n" f f;

       out "clean:@\n";
       out "\trm -f coq/*.vo@\n@\n";
    )
    (full ^ ".makefile")

let makefile f =
  let c = Filename.basename f in
  generic f c [c]



(*
Local Variables:
compile-command: "make -C .. bin/jessie.byte"
End:
*)
