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
       let name = "Jessie2"
       let shortname = "Jessie2"
       let help = "Translation to Jessie(2) intermediate language with subsequent launch of Jessie-to-Why3ML translator"
     end)

module Project_name =
  Empty_string
    (struct
       let option_name = "-jessie-file-name"
       let arg_name = ""
       let help = "specify output file name for Jessie-to-Why3ML translator. The default is the input .c file name or \
                   `whole_program' in case of several input files"
     end)

module Behavior =
  Empty_string
    (struct
       let option_name = "-jessie-behavior"
       let arg_name = ""
       let help = "restrict verification to a specific behavior (safety, default or a user-defined behavior)"
     end)

module Analysis =
  False
    (struct
      let option_name = "-jessie"
      let help = "perform C-to-Jessie translation, i.e. this option is used to launch the plugin"
    end)

module Force_ad_hoc_normalization =
  False
    (struct
      let option_name = "-jessie-ad-hoc-normalization"
      let help = "enforce additional code normalization (obsolete, deprecated)."
    end)

let () =
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
  String_set
    (struct
      let option_name = "-jessie-jc-opt"
      let arg_name = ""
      let help = "give an option to Jessie-to-Why3ML translator (e.g., -jessie-jc-opt=\"-forall-inst-bound 5\")"
    end)

module Why3_opt =
  String_set
    (struct
       let option_name = "-jessie-why3-opt"
       let arg_name = ""
       let help = "give an option to Why3 (e.g., -jessie-why3-opt=\"--debug fast-wp\")"
     end)

module Gen_only =
  False
    (struct
      let option_name = "-jessie-gen-only"
      let help = "only generate Jessie code (for developer use)"
    end)

module Cpu_limit =
  Zero
    (struct
       let option_name = "-jessie-cpu-limit"
       let arg_name = ""
       let help = "set the time limit in sec. for the analysis (suitable only for some targets, see -jessie-target)"
     end)

module Target =
  String
    (struct
       let option_name = "-jessie-target"
       let default = "why3ide"
       let arg_name = ""
       let help = "run Make with the specified target instead of the default `why3ide'. Use `update' to simply \
                   generate the .mlw file and exit"
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
