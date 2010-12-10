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



type prover_id =
  | Simplify | Harvey | Cvcl | Zenon | Rvsat | Yices | Ergo | ErgoSelect
  | Cvc3 | SimplifySelect | Z3 | Gappa | GappaSelect
  | Coq | PVS | VeriT

type lazy_regexp =
  {
    regexp : string;
    mutable cregexp  : Str.regexp option;
  }

let make_regexp s = { regexp = s; cregexp = None }

type prover_data =
  {
    name : string;
    is_interactive : bool;
    mutable version: string;
    version_switch : string;
    version_regexp : string;
    versions_ok : string list;
    versions_old : string list;
    mutable command : string;
    command_switches : string;
    valid_regexp : lazy_regexp option;
    (* when None, validity is checked by testing return code == 0 *)
    undecided_regexp : lazy_regexp;
    stdin_switch : string option;
  }

let gappa =
  {
    name = "Gappa";
    is_interactive = false;
    version = "";
    version_switch = "--version";
    version_regexp = "Gappa \\([^ ]*\\)";
    versions_ok = ["0.13.0"];
    versions_old = ["0.11.2";"0.12.0";"0.12.1";"0.12.2";"0.12.3"];
    command = "gappa";
    command_switches = "";
    valid_regexp = None; (* valid iff return code = 0 *)
    undecided_regexp = make_regexp "no contradiction was found\\|some enclosures were not satisfied";
    stdin_switch = None;
  }

let alt_ergo =
  {
    name = "Alt-Ergo";
    is_interactive = false;
    version = "";
    version_switch = "-version";
    version_regexp = ".*Ergo \\([^ ]*\\)";
    versions_ok = ["0.91"; "0.92.1"; "0.92.2"];
    versions_old = ["0.8"; "0.9"];
    command = "alt-ergo";
    command_switches = "";
    valid_regexp = Some (make_regexp "\\bValid\\b");
    undecided_regexp = make_regexp "\\bI don't know\\b\\|\\bInvalid\\b";
    stdin_switch = None;
  }

let simplify =
  {
    name = "Simplify";
    is_interactive = false;
    version = "";
    version_switch = "-version";
    version_regexp = "Simplify version \\([^ ,]+\\)";
    versions_ok = ["1.5.4";"1.5.5"];
    versions_old = [""];
    command = "Simplify";
    command_switches = "";
    valid_regexp = Some (make_regexp "\\bValid\\b");
    undecided_regexp = make_regexp "\\bInvalid\\b";
    stdin_switch = None;
  }

let z3 =
  {
    name = "Z3";
    is_interactive = false;
    version = "";
    version_switch = "-version";
    version_regexp = "Z3 version \\([^ \r]+\\)";
    versions_ok = ["2.2"];
    versions_old = ["2.1";"1.3"];
    command = "z3";
    command_switches = "-smt ";
    valid_regexp = Some (make_regexp "\\bunsat\\b");
    undecided_regexp = make_regexp "\\bunknown\\b\\|\\bsat\\b|\\bFail\\b";
    stdin_switch = Some "-in";
  }


let yices =
  {
    name = "Yices";
    is_interactive = false;
    version = "";
    version_switch = "--version";
    version_regexp = "[Yices ]*\\([0-9.]+\\)";
    versions_ok = ["1.0.17";"1.0.24"];
    versions_old = [""];
    command = "yices";
    command_switches = "-smt ";
    valid_regexp = Some (make_regexp "\\bunsat\\b");
    undecided_regexp = make_regexp "\\bunknown\\b\\|\\bsat\\b\\|feature not supported: non linear problem";
    stdin_switch = Some "";
  }

let cvc3 =
  {
    name = "CVC3";
    is_interactive = false;
    version = "";
    version_switch = "-version";
    version_regexp = "This is CVC3 version \\([^ ]+\\)";
    versions_ok = ["2.2"];
    versions_old = ["2.1"];
    command = "cvc3";
    command_switches = "-lang smt ";
    valid_regexp = Some (make_regexp "\\bunsat\\b");
    undecided_regexp = make_regexp "\\bunknown\\b\\|\\bsat\\b";
    stdin_switch = Some "";
  }

let verit =
{
  name = "VeriT";
  is_interactive = false;
  version = "";
  version_switch = "--proof-format-and-exit";
  (* ugly, but with --help everything is
     output on stderr *)
  version_regexp = "verit *\\([0-9.]+\\(rc[0-9]*\\)?\\)";
  versions_ok = [""];
  versions_old = [""];
  command="verit";
  command_switches="--enable-simp --enable-unit-simp --enable-unit-subst-simp --enable-qnt-simp --split-on-demand";
  valid_regexp = Some (make_regexp "\\bunsat\\b");
  undecided_regexp = make_regexp "\\bunknown\\b\\|\\bsat\\b";
  stdin_switch = Some ""
}

let cvcl =
  {
    name = "CVCL";
    is_interactive = false;
    version = "";
    version_switch = "-version";
    version_regexp = "This is CVC3 version \\([^ ]+\\)";
    versions_ok = ["2.2"];
    versions_old = ["2.1"];
    command = "cvc3";
    command_switches = "";
    valid_regexp = Some (make_regexp "\\bValid\\b");
    undecided_regexp = make_regexp "\\bUnknown\\b\\|\\bError\\b";
    stdin_switch = Some "";
  }

let coq =
  {
    name = "Coq";
    is_interactive = true;
    version = "";
    version_switch = "-v";
    version_regexp = "The Coq Proof Assistant, version \\([^ ]+\\)";
    versions_ok = ["8.0"; "8.1";"8.2";"8.2pl1"];
    versions_old = ["7.4"];
    command = "coqc";
    command_switches = "";
    valid_regexp = None;
    undecided_regexp = make_regexp "Error while reading";
    stdin_switch = None;
  }

let pvs =
  {
    name = "PVS";
    is_interactive = true;
    version = "";
    version_switch = "-version";
    version_regexp = "PVS Version \\([^ ]+\\)";
    versions_ok = ["4.1"];
    versions_old = [];
    command = "pvs";
    command_switches = "-batch";
    valid_regexp = None;
    undecided_regexp = make_regexp "Error";
    stdin_switch = None;
  }


let prover_list =
  [
    Ergo, (alt_ergo, ["alt-ergo" ; "ergo"]) ;
    Simplify, (simplify, ["Simplify" ; "simplify"]) ;
    Z3, (z3, ["z3"]) ;
    Yices, (yices, ["yices"]) ;
    Cvc3, (cvc3, ["cvc3"]) ;
    Cvcl, (cvcl, ["cvcl"]) ;
    Gappa, (gappa, ["gappa"]) ;
    Coq, (coq, ["coqc"]);
    PVS, (pvs, ["pvs"]);
    VeriT, (verit, ["verit"]);
  ]

let rc_file () =
  let home = Rc.get_home_dir () in
  Filename.concat home ".whyrc"

open Format

let load_prover_info p key l =
  List.iter
    (function
       | ("version",Rc.RCstring s) -> p.version <- s
       | ("command",Rc.RCstring s) -> p.command <- s
       | (field,_) ->
	   printf "Unknown field `%s' in section [%s] of rc file@." field key)
    l

let already_loaded = ref false

let load_rc_file () =
  if !already_loaded then () else
  let rc_file = rc_file () in
  let rc = Rc.from_file rc_file in
  List.iter
    (fun (key,args) ->
       match key with
	 | "Alt-Ergo" -> load_prover_info alt_ergo key args
	 | "Simplify" -> load_prover_info simplify key args
	 | "Z3" -> load_prover_info z3 key args
	 | "Yices" -> load_prover_info yices key args
	 | "CVC3" -> load_prover_info cvc3 key args
         | "CVCL" -> load_prover_info cvcl key args
	 | "Gappa" -> load_prover_info gappa key args
	 | "Coq" -> load_prover_info coq key args
	 | "PVS" -> load_prover_info pvs key args
         | "VeriT" -> load_prover_info verit key args
	 | _ ->
	     printf "Unknown section [%s] in config file '%s'@." key rc_file)
    rc;
  already_loaded := true


let save_prover_info fmt p =
  fprintf fmt "[%s]@." p.name;
  fprintf fmt "version = \"%s\"@." p.version;
  fprintf fmt "command = \"%s\"@." p.command;
  fprintf fmt "@."

let save_rc_file () =
  let ch = open_out (rc_file ()) in
  let fmt = Format.formatter_of_out_channel ch in
  List.iter (fun (_,(p,_)) -> save_prover_info fmt p) prover_list;
  close_out ch
