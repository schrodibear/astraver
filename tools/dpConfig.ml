(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



type prover_id = 
    Simplify | Harvey | Cvcl | Zenon | Rvsat | Yices | Ergo | ErgoSelect
  | Cvc3 | SimplifySelect | Z3 | Coq | Gappa | GappaSelect

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
    mutable command : string;
    command_switches : string;
    valid_regexp : lazy_regexp option;
    (* when None, validity is checked by testing return code == 0 *)
    undecided_regexp : lazy_regexp;
  }
    
let gappa =
  {
    name = "Gappa";
    is_interactive = false;
    version = "";
    version_switch = "--version";
    version_regexp = "Gappa \\([^ ]*\\)";
    command = "gappa";
    command_switches = "";
    valid_regexp = None; (* valid iff return code = 0 *)
    undecided_regexp = make_regexp "no contradiction was found\\|some enclosures were not satisfied";
  }

let alt_ergo =
  {
    name = "Alt-Ergo";
    is_interactive = false;
    version = "";
    version_switch = "-version";
    version_regexp = ".*Ergo \\([^ ]*\\)";
    command = "alt-ergo";
    command_switches = "";
    valid_regexp = Some (make_regexp "\\bValid\\b");
    undecided_regexp = make_regexp "\\bI don't know\\b\\|\\bInvalid\\b";
  }

let simplify = 
  {
    name = "Simplify";
    is_interactive = false;
    version = "";
    version_switch = "-version";
    version_regexp = "Simplify version \\([^ ,]+\\)";
    command = "Simplify";
    command_switches = "";
    valid_regexp = Some (make_regexp "\\bValid\\b");
    undecided_regexp = make_regexp "\\bInvalid\\b";
  }

let z3 =
  {
    name = "Z3";
    is_interactive = false;
    version = "";
    version_switch = "-version";
    version_regexp = "Z3 version \\([^ \r]+\\)";
    command = "z3";
    command_switches = "-smt";
    valid_regexp = Some (make_regexp "\\bunsat\\b");
    undecided_regexp = make_regexp "\\bunknown\\b\\|\\bsat\\b";
  }


let yices =    
  {
    name = "Yices";
    is_interactive = false;
    version = "";
    version_switch = "--version";
    version_regexp = "\\([^ ]+\\)";
    command = "yices";
    command_switches = "-pc 0 -smt ";
    valid_regexp = Some (make_regexp "\\bunsat\\b");
    undecided_regexp = make_regexp "\\bunknown\\b\\|\\bsat\\b\\|feature not supported: non linear problem";
  }

let cvc3 =    
  {
    name = "CVC3";
    is_interactive = false;
    version = "";
    version_switch = "-version";
    version_regexp = "This is CVC3 version \\([^ ]+\\)";
    command = "cvc3";
    command_switches = "-lang smt ";
    valid_regexp = Some (make_regexp "\\bunsat\\b");
    undecided_regexp = make_regexp "\\bunknown\\b\\|\\bsat\\b";
  }

let coq =    
  {
    name = "Coq";
    is_interactive = true;
    version = "";
    version_switch = "-v";
    version_regexp = "The Coq Proof Assistant, version \\([^ ]+\\)";
    command = "coqc";
    command_switches = "";
    valid_regexp = None;
    undecided_regexp = make_regexp "Error while reading";
  }


let prover_list = 
  [
    Ergo, (alt_ergo, ["alt-ergo" ; "ergo"]) ;
    Simplify, (simplify, ["Simplify" ; "simplify"]) ;
    Z3, (z3, ["z3"]) ;
    Yices, (yices, ["yices"]) ;
    Cvc3, (cvc3, ["cvc3"]) ;
    Coq, (coq, ["coqc"]);
    Gappa, (gappa, ["gappa"]) ;
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
	 | "Coq" -> load_prover_info coq key args
	 | "Gappa" -> load_prover_info gappa key args
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

