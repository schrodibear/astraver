(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

open Format
open Cversion
open Unix

let c = match Sys.argv with
  | [| _; f |] -> open_out f
  | _ -> eprintf "usage: cadlog file@."; exit 1

let fmt = formatter_of_out_channel c

let d,m,y =
  let tm = localtime (time ()) in
    tm.tm_mday, 1+tm.tm_mon, tm.tm_year

let () =
  fprintf fmt "Caduceus version: %s@." version;
  fprintf fmt "Caduceus compilation date: %s@." date;
  fprintf fmt "Caduceus compilation date: %d/%d/%d@." d m y;
  try
    while true do
      let s = read_line () in
	print_endline s;
	fprintf fmt "%s@." s
    done
  with End_of_file ->
    close_out c
