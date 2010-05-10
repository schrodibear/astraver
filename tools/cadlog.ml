(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2010                                               *)
(*                                                                        *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Jean-Christophe FILLIATRE, CNRS                                     *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
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

open Format
open Unix

let usage_string = "cadlog [options] file"

let usage () =
  eprintf "usage: %s@." usage_string;
  exit 1

let file = ref ""

let def_file s =
  if !file="" then file := s
  else usage () 
  
let jessie = ref false

let krakatoa = ref false

let _ = 
  Arg.parse 
      [ "-jc", Arg.Set jessie, "  Jessie bench";
	"-java", Arg.Set krakatoa, "  Krakatoa bench";
      ]
      def_file usage_string

let file = if !file ="" then usage() else !file

let c = open_out file

let fmt = formatter_of_out_channel c

let tool = 
  if !jessie then "Jessie" else 
  if !krakatoa then "Krakatoa" else 
    "Caduceus"

let version,date =
  if !jessie || !krakatoa 
  then Version.version, Version.date else 
    Cversion.version, Cversion.date

let d,m,y =
  let tm = localtime (time ()) in
    tm.tm_mday, 1+tm.tm_mon, 1900+tm.tm_year

let () =
  fprintf fmt "%8s version         : %s@." tool version;
  fprintf fmt "%8s compilation date: %s@." tool date;
  fprintf fmt "Bench execution date     : %d/%d/%d@." d m y;
  try
    while true do
      let s = read_line () in
	print_endline s;
	fprintf fmt "%s@." s
    done
  with End_of_file ->
    close_out c
