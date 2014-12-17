(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
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

module Project_name =
  EmptyString
    (struct
       let option_name = "-jessie-project-name"
       let arg_name = ""
       let help = "specify project name for Jessie analysis"
     end)

module Behavior =
  EmptyString
    (struct
       let option_name = "-jessie-behavior"
       let arg_name = ""
       let help =
	 "restrict verification to a specific behavior (safety, default or a user-defined behavior)"
     end)

module Analysis =
  False
    (struct
      let option_name = "-jessie"
      let help = "perform C to Jessie translation"
    end)

module Force_ad_hoc_normalization =
  False
    (struct
      let option_name = "-jessie-adhoc-normalization"
      let help =
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
  Force_ad_hoc_normalization.add_set_hook
    (fun _ b ->
       if b then begin
	 Kernel.SimplifyCfg.on ();
	 Kernel.KeepSwitch.on ();
	 Kernel.Constfold.on ();
	 Kernel.PreprocessAnnot.on ();
	 Cabs2cil.setDoTransformWhile ();
	 Cabs2cil.setDoAlternateConditional ();
       end);
  State_dependency_graph.add_dependencies
    ~from:Force_ad_hoc_normalization.self
    [
      Kernel.SimplifyCfg.self;
      Kernel.KeepSwitch.self;
      Kernel.Constfold.self;
      Kernel.PreprocessAnnot.self
    ]

let () =
  Analysis.add_set_hook (fun _ b -> Force_ad_hoc_normalization.set b);
  State_dependency_graph.add_dependencies
    ~from:Analysis.self [Force_ad_hoc_normalization.self]

module Jc_opt =
  StringSet
    (struct
      let option_name = "-jessie-jc-opt"
      let arg_name = ""
      let help = "give an option to Jc (e.g., -jessie-jc-opt=\"-trust-ai\")"
    end)

module Why_opt =
  StringSet
    (struct
       let option_name = "-jessie-why-opt"
       let arg_name = ""
       let help = "give an option to Why (e.g., -jessie-why-opt=\"-fast-wp\")"
     end)

module Why3_opt =
  StringSet
    (struct
       let option_name = "-jessie-why3-opt"
       let arg_name = ""
       let help = "give an option to Why3 (e.g., -jessie-why3-opt=\"--debug fast-wp\")"
     end)

module Gen_only =
  False
    (struct
      let option_name = "-jessie-gen-only"
      let help = "only generates jessie code (for developer use)"
    end)

module Infer_annot =
  EmptyString
    (struct
       let option_name = "-jessie-infer-annot"
       let arg_name = ""
       let help = "infer function annotations (inv, pre, spre, wpre)"
     end)

module Cpu_limit =
  Zero
    (struct
       let option_name = "-jessie-cpu-limit"
       let arg_name = ""
       let help = "set the time limit in sec. for the analysis"
     end)

module Abs_domain =
  String
    (struct
       let option_name = "-jessie-abstract-domain"
       let default = "poly"
       let arg_name = ""
       let help = "use specified abstract domain (box, oct or poly)"
     end)

module Atp =
  String
    (struct
       let option_name = "-jessie-atp"
       let default = "why3ide"
       let arg_name = ""
       let help = "use given automated theorem prover, among `alt-ergo', `cvc3', `simplify', `vampire', `yices' and `z3'. Use `goals' to simply generate goals in Why syntax."
     end)

module Hint_level =
  Zero
    (struct
       let option_name = "-jessie-hint-level"
       let arg_name = ""
       let help = "level of hints, i.e. assertions to help the proof (e.g. for string usage)"
     end)

module Specialize =
  True
    (struct
      let option_name = "-jessie-specialize"
      let help = "generate specialized versions for block-level functions e.g. memcpy"
     end)

module Extract =
  True
    (struct
      let option_name = "-jessie-extract"
      let help = "process only explicitly annotated functions with their dependencies"
     end)

module Flat_vararg =
  False
    (struct
      let option_name = "-jessie-flat-vararg"
      let help = "use flat void * array to represent variadic arguments"
     end)
(*
Local Variables:
compile-command: "make"
End:
*)
