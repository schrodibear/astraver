(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: loc.ml,v 1.7 2003-12-05 15:49:30 filliatr Exp $ i*)

(*s Error locations. *)

type t = int * int

let dummy = (0,0)

let join (b,_) (_,e) = (b,e)

let file = ref (None : string option)

let set_file f = file := Some f

let with_file f = match !file with Some x -> f x | None -> ()

(*s Error reporting. *)

let linenum f b =
  let cin = open_in f in
  let rec lookup n l cl =
    if n = b then 
      (l,cl)
    else 
      let c = input_char cin in
      lookup (succ n) (if c == '\n' then succ l else l) 
	(if c == '\n' then 0 else succ cl)
  in
  lookup 0 1 0

open Format

let report fmt (b,e) = match !file with
  | None ->
      fprintf fmt "Standard input, characters %d-%d:\n" b e
  | Some f ->
      (try
         let (l,cl) = linenum f b in
         fprintf fmt "File \"%s\", line %d, characters %d-%d:@\n" 
	   f l cl (cl+e-b)
       with _ ->
	 fprintf fmt "File \"%s\", characters %d-%d:@\n" f b e)

let report_obligation fmt (b,e) = match !file with
  | None -> 
      fprintf fmt "Why obligation from standard input, characters %d-%d" b e
  | Some f ->
      fprintf fmt "Why obligation from file \"%s\", characters %d-%d" f b e

(*s Line number *)

let report_line fmt n =
  with_file 
    (fun f ->
       let cin = open_in f in
       let l = ref 1 in
       let rec loop i =
	 if i != n then begin 
	   let c = input_char cin in 
	   if c == '\n' then incr l;
	   loop (succ i) 
	 end
       in
       begin try loop 0 with End_of_file -> () end;
       close_in cin;
       fprintf fmt "%s:%d: " f !l)



