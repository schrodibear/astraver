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
       let name = "AstraVer"
       let shortname = "av"
       let help = "Deductive verification plugin based on translation to Why3ML, successor of Jessie"
     end)

let astraver = add_group "astraver"

module Project_name =
  Empty_string
    (struct
       let option_name = "-av-file-name"
       let arg_name = ""
       let help =
         "specify output file name for AstraVer-to-Why3ML translator. The default is the input .c file name or \
          `whole_program' in case of several input files"
     end)

module Output_Dir_name =
  Empty_string
    (struct
       let option_name = "-av-out"
       let arg_name = ""
       let help = "specify output dirname for AstraVer-to-Why3ML translator."
     end)

module Behavior =
  Empty_string
    (struct
       let option_name = "-av-behavior"
       let arg_name = ""
       let help = "restrict verification to a specific behavior (safety, default or a user-defined behavior)"
     end)

module Analysis =
  False
    (struct
      let option_name = "-av"
      let help = "perform C-to-AstraVer translation, i.e. this option is used to launch the plugin"
    end)

module Force_ad_hoc_normalization =
  False
    (struct
      let option_name = "-av-ad-hoc-normalization"
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

let () = Parameter_customize.set_group astraver
let () = Parameter_customize.no_category ()

module Av_opt =
  String_set
    (struct
      let option_name = "-av-opt"
      let arg_name = ""
      let help = "give an option to AstraVer Jessie-to-Why3ML translator (e.g., -av-opt=\"-forall-inst-bound 5\")"
    end)

let () = Parameter_customize.set_group astraver
let () = Parameter_customize.no_category ()

module Why3_opt =
  String_set
    (struct
       let option_name = "-av-why3-opt"
       let arg_name = ""
       let help = "give an option to Why3 (e.g., -av-why3-opt=\"--debug fast-wp\")"
     end)

module Gen_only =
  False
    (struct
      let option_name = "-av-gen-only"
      let help = "only generate AstraVer code (for developer use)"
    end)

module Cpu_limit =
  Zero
    (struct
       let option_name = "-av-cpu-limit"
       let arg_name = ""
       let help = "set the time limit in sec. for the analysis (suitable only for some targets, see -av-target)"
     end)

module Target =
  String
    (struct
       let option_name = "-av-target"
       let default = "why3ide"
       let arg_name = ""
       let help = "run Make with the specified target instead of the default `why3ide'. Use `update' to simply \
                   generate the .mlw file and exit"
     end)

module Specialize =
  True
    (struct
      let option_name = "-av-specialize"
      let help = "generate specialized versions for block-level functions e.g. memcpy"
     end)

module Extract =
  True
    (struct
      let option_name = "-av-extract"
      let help = "process only explicitly annotated functions with their dependencies"
     end)

module Flat_vararg =
  False
    (struct
      let option_name = "-av-flat-vararg"
      let help = "use flat void * array to represent variadic arguments"
     end)
(*
Local Variables:
compile-command: "make"
End:
*)
