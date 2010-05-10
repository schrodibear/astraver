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
       let descr = "translation to jessie (experimental)"
     end)

module ProjectName =
  EmptyString
    (struct
       let option_name = "-jessie-project-name"
       let arg_name = ""
       let descr = "specify project name for Jessie analysis"
     end)

module Behavior =
  EmptyString
    (struct
       let option_name = "-jessie-behavior"
       let arg_name = ""
       let descr =
	 "restrict verification to a specific behavior (safety, default or a user-defined behavior)"
     end)

module Analysis =
  False(struct
	  let option_name = "-jessie"
	  let descr = "perform C to Jessie translation"
	end)

module ForceAdHocNormalization =
  False(struct
          let option_name = "-jessie-adhoc-normalization"
          let descr =
            "enforce code normalization in a mode suitable for Jessie plugin."
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
	 Parameters.SimplifyCfg.on ();
	 Parameters.KeepSwitch.on ();
	 Parameters.Constfold.on ();
	 Parameters.PreprocessAnnot.on ();
	 Cabs2cil.setDoTransformWhile ();
	 Cabs2cil.setDoAlternateConditional ();
       end);
  Parameters.SimplifyCfg.depend ForceAdHocNormalization.self;
  Parameters.KeepSwitch.depend ForceAdHocNormalization.self;
  Parameters.Constfold.depend ForceAdHocNormalization.self;
  Parameters.PreprocessAnnot.depend ForceAdHocNormalization.self

let () =
  Analysis.add_set_hook (fun _ b -> ForceAdHocNormalization.set b);
  ForceAdHocNormalization.depend Analysis.self

module JcOpt =
  StringSet(struct
	      let option_name = "-jessie-jc-opt"
	      let module_name = "-jessie-jc-opt"
	      let arg_name = ""
	      let descr = "give an option to Jc (e.g., -jessie-jc-opt=\"-trust-ai\")"
	    end)

module WhyOpt =
  StringSet
    (struct
       let option_name = "-jessie-why-opt"
       let module_name = "-jessie-why-opt"
       let arg_name = ""
       let descr = "give an option to Why (e.g., -jessie-why-opt=\"-fast-wp\")"
     end)

module GenOnly =
  False(struct
	  let option_name = "-jessie-gen-only"
	  let module_name = "-jessie-gen-only"
	  let descr = "only generates jessie code (for developer use)"
	end)

module InferAnnot =
  EmptyString
    (struct
       let option_name = "-jessie-infer-annot"
       let module_name = "-jessie-infer-annot"
       let arg_name = ""
       let descr = "infer function annotations (inv, pre, spre, wpre)"
     end)

module CpuLimit =
  Zero
    (struct
       let option_name = "-jessie-cpu-limit"
       let module_name = "-jessie-cpu-limit"
       let arg_name = ""
       let descr = "set the time limit in sec. for the analysis"
     end)

module AbsDomain =
  String
    (struct
       let option_name = "-jessie-abstract-domain"
       let module_name = "-jessie-abstract-domain"
       let default = "poly"
       let arg_name = ""
       let descr = "use specified abstract domain (box, oct or poly)"
     end)

module Atp =
  String
    (struct
       let option_name = "-jessie-atp"
       let module_name = "-jessie-atp"
       let default = "gui"
       let arg_name = ""
       let descr = "use given automated theorem prover, among `alt-ergo', `cvc3', `simplify', `yices' and `z3'. Use `goals' to simply generate goals in Why syntax."
     end)

module HintLevel =
  Zero
    (struct
       let option_name = "-jessie-hint-level"
       let module_name = "-jessie-hint-level"
       let arg_name = ""
       let descr = "level of hints, i.e. assertions to help the proof (e.g. for string usage)"
     end)

(*
Local Variables:
compile-command: "LC_ALL=C make"
End:
*)
