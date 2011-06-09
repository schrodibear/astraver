(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2010                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS                                     *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*    Thierry HUBERT, Univ. Paris-sud 11                                  *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
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

include
  Plugin.Register
    (struct
       let name = "jessie"
       let shortname = "jessie"
       let help = "translation to Why/Jessie"
     end)

module ProjectName =
  EmptyString
    (struct
       let option_name = "-jessie-project-name"
       let arg_name = ""
       let help = "specify project name for Jessie analysis"
       let kind = `Tuning
     end)

module Behavior =
  EmptyString
    (struct
       let option_name = "-jessie-behavior"
       let arg_name = ""
       let help =
	 "restrict verification to a specific behavior (safety, default or a user-defined behavior)"
       let kind = `Correctness
     end)

module Analysis =
  False(struct
	  let option_name = "-jessie"
	  let help = "perform C to Jessie translation"
          let kind = `Tuning
	end)

module ForceAdHocNormalization =
  False(struct
          let option_name = "-jessie-adhoc-normalization"
          let help =
            "enforce code normalization in a mode suitable for Jessie plugin."
          let kind = `Tuning
        end)

let () =
  (* [JS 2009/10/04]
     Preserve the behaviour of svn release <= r5012.
     However it works only if the int-model is set from the command line.
     [CM 2009/12/08]
     setting int-model on the command-line is obsolete, so what is this
     code for ?
  *)
  ForceAdHocNormalization.add_set_hook
    (fun _ b ->
       if b then begin
	 Kernel.SimplifyCfg.on ();
	 Kernel.KeepSwitch.on ();
	 Kernel.Constfold.on ();
	 Kernel.PreprocessAnnot.on ();
	 Cabs2cil.setDoTransformWhile ();
	 Cabs2cil.setDoAlternateConditional ();
       end);
  State_dependency_graph.Static.add_dependencies
    ~from:ForceAdHocNormalization.self
    [ Kernel.SimplifyCfg.self;
      Kernel.KeepSwitch.self;
      Kernel.Constfold.self;
      Kernel.PreprocessAnnot.self ]

let () =
  Analysis.add_set_hook (fun _ b -> ForceAdHocNormalization.set b);
  State_dependency_graph.Static.add_dependencies
    ~from:Analysis.self [ ForceAdHocNormalization.self ]

module JcOpt =
  StringSet(struct
	      let option_name = "-jessie-jc-opt"
	      let module_name = "-jessie-jc-opt"
	      let arg_name = ""
	      let help = "give an option to Jc (e.g., -jessie-jc-opt=\"-trust-ai\")"
              let kind = `Tuning
	    end)

module WhyOpt =
  StringSet
    (struct
       let option_name = "-jessie-why-opt"
       let module_name = "-jessie-why-opt"
       let arg_name = ""
       let help = "give an option to Why (e.g., -jessie-why-opt=\"-fast-wp\")"
       let kind = `Tuning
     end)

module GenOnly =
  False(struct
	  let option_name = "-jessie-gen-only"
	  let module_name = "-jessie-gen-only"
	  let help = "only generates jessie code (for developer use)"
          let kind = `Tuning
	end)

module InferAnnot =
  EmptyString
    (struct
       let option_name = "-jessie-infer-annot"
       let module_name = "-jessie-infer-annot"
       let arg_name = ""
       let help = "infer function annotations (inv, pre, spre, wpre)"
       let kind = `Correctness
     end)

module CpuLimit =
  Zero
    (struct
       let option_name = "-jessie-cpu-limit"
       let module_name = "-jessie-cpu-limit"
       let arg_name = ""
       let help = "set the time limit in sec. for the analysis"
       let kind = `Tuning
     end)

module AbsDomain =
  String
    (struct
       let option_name = "-jessie-abstract-domain"
       let module_name = "-jessie-abstract-domain"
       let default = "poly"
       let arg_name = ""
       let help = "use specified abstract domain (box, oct or poly)"
       let kind = `Tuning
     end)

module Atp =
  String
    (struct
       let option_name = "-jessie-atp"
       let module_name = "-jessie-atp"
       let default = "gui"
       let arg_name = ""
       let help = "use given automated theorem prover, among `alt-ergo', `cvc3', `simplify', `vampire', `yices' and `z3'. Use `goals' to simply generate goals in Why syntax."
       let kind = `Tuning
     end)

module HintLevel =
  Zero
    (struct
       let option_name = "-jessie-hint-level"
       let module_name = "-jessie-hint-level"
       let arg_name = ""
       let help = "level of hints, i.e. assertions to help the proof (e.g. for string usage)"
       let kind = `Tuning
     end)

(*
Local Variables:
compile-command: "make"
End:
*)
