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

type input_kind = Ml | Mli

let input_files = ref []

let output_file = ref None

(******************************************************************************)

let input_file t n = input_files := (t, n) :: !input_files

let spec = Arg.align [
  "-ml", Arg.String(input_file Ml),
  "<file> Input file assuming it is a structure";
  "-mli", Arg.String(input_file Mli),
  "<file> Input file assuming it is a signature";
  "-o", Arg.String(fun s -> output_file := Some s),
  "<file> Output file"
]

let file_ext f =
  let i = ref (String.length f - 1) in
  while !i >= 0 && f.[!i] <> '.' do i := !i - 1 done;
  match if !i < 0 then "" else String.sub f !i (String.length f - !i) with
    | ".mli" -> Mli
    | _ -> Ml

let anon_fun s = input_file (file_ext s) s

let usage_msg = "jessica [options] files"

let _ =
  Arg.parse spec anon_fun usage_msg

(******************************************************************************)

let default_filename = match !input_files with
  | [] -> "jessica_out.jc"
  | (_, x)::_ -> Filename.chop_extension x ^ ".jc"

let input_files = List.rev !input_files

let rec list_last_snd def = function
  | [] -> def
  | [ x ] -> snd x
  | _::tl -> list_last_snd def tl

let output_file = match !output_file with
  | Some filename -> filename
  | None -> default_filename

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
