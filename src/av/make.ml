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

open Format
open Pp

let generic full _f targets =
  print_in_file
    (fun fmt ->
       let out x = fprintf fmt x in
       out "# this makefile was automatically generated; do not edit @\n@\n";
       out "TIMEOUT ?= 10@\n@\n";
       out "WHYLIB ?= %s@\n@\n" (String.escaped Options.libdir);
       out "USERWHYTHREEOPT=%s@\n"  (Options.why3_opt);
       out "@\n";
       out "JESSIE3CONF ?= $(WHYLIB)/why3/why3.conf@\n@\n";

       let why3ml_target =
	 (match targets with f :: _ -> f ^ ".mlw" | [] -> "")
       in
       out "why3ml: %s@\n" why3ml_target;
       out "\t why3 $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<@\n@\n";

       out "why3ide: %s@\n" why3ml_target;
       out "\t why3 ide $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<@\n@\n";

       out "why3replay: %s@\n" why3ml_target;
       out "\t why3 replay $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<@\n@\n";

       out "why3autoreplay: %s@\n" why3ml_target;
       out "\t why3 replay -q -f --obsolete-only $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<@\n@\n";

       out "why3typecheck: %s@\n" why3ml_target;
       out "\t why3 prove --type-only $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<@\n@\n";

       out "why3prove: %s@\n" why3ml_target;
       out "\t why3 prove $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<@\n@\n";

       out "why3sprove: %s@\n" why3ml_target;
       out "\t why3 sprove --strategy default $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<@\n@\n";
    )
    (full ^ ".makefile")

let makefile f =
  let c = Filename.basename f in
  generic f c [c]
