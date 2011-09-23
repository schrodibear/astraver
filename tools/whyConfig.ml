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
open DpConfig

let provers_found = ref 0

let prover_tips_info = ref false

let rec detect_prover p cmds =
  match cmds with
    | [] ->
	printf "detection of prover %s failed@." p.name
    | cmd::rem ->
	let out = Filename.temp_file "out" "" in
        let cmd2 = cmd ^ " " ^ p.version_switch in
	let c = cmd2 ^ " > " ^ out in
	let ret = Sys.command c in
	if ret <> 0
          (* was needed for older version of gappa, but is
	     wrong under windows: && not (p == gappa && ret = 1) *)
        then
	  begin
	    printf "command '%s' failed@." cmd2;
	    detect_prover p rem
	  end
	else
	  let s =
            try
              let ch = open_in out in
              let s = ref (input_line ch) in
              while !s = "" do s := input_line ch done;
              close_in ch;
	      Sys.remove out;
              !s
            with Not_found | End_of_file  -> ""
          in
	  let re = Str.regexp p.version_regexp in
	  if Str.string_match re s 0 then
	    let nam = p.name in
	    let ver = Str.matched_group 1 s in
            begin
              if List.mem ver p.versions_ok then
	        printf "Found prover %s version %s, OK.@." nam ver
              else
                begin
                  prover_tips_info := true;
                  if List.mem ver p.versions_old then
                    printf "Warning: prover %s version %s is quite old, please consider upgrading to a newer version.@." nam ver
                  else
                    printf "Warning: prover %s version %s is not known to be supported, use it at your own risk!@." nam ver
                end
            end;
	    p.command <- cmd;
	    p.version <- ver;
            incr provers_found
	  else
	    begin
              prover_tips_info := true;
	      printf "Warning: found prover %s but name/version not recognized by regexp `%s'@." p.name p.version_regexp;
	      printf "Answer was `%s'@." s;
	      p.command <- cmd;
	      p.version <- "?";
	    end


let main () =
  begin
    try
      load_rc_file ()
    with Not_found ->
      printf "rc file not found, using default values for provers@\n@.";
  end;
  printf "starting autodetection...@.";
  List.iter (fun (_,(p,l)) ->
               (* we reset version because it might have been read in .whyrc *)
               p.version <- "";
               let l =
                 if List.mem p.command l then l else l@[p.command]
               in
               detect_prover p l) prover_list;
  printf "detection done.@.";
  if !provers_found = 0 then
    begin
      printf "No provers found! you need to install at least one prover.@.";
      prover_tips_info := true
    end
  else
    begin
      printf "writing rc file `%s'...@\n@." (rc_file());
      save_rc_file ();
      printf "    prover      version              info   invocation@.";
      printf "------------------------------------------------------@.";
      List.iter (fun (_,(p,_)) ->
                   let nam = p.name in
                   let ver = p.version in
                   let morever =
                     if p.version = "" then "not found" else
                       if p.version = "?" then "undetected" else
                         if List.mem p.version p.versions_ok then "" else
                           if List.mem p.version p.versions_old then "(obsolete)" else
                             "(not supported)"
                   in
                   printf "%10s   %10s   %15s   %s@." nam ver morever
                     (if p.version ="" then "" else
                      p.command ^ " " ^ p.command_switches);
                ) prover_list;
      printf "------------------------------------------------------@.";
    end;
  if !prover_tips_info then
    begin
      printf "See web page http://why.lri.fr/provers.en.html for up-to-date information about provers and their versions@."
    end

let () = Printexc.catch main ()




