
(*i $Id: loc.ml,v 1.3 2001-08-24 19:07:17 filliatr Exp $ i*)

(*s Error locations. *)

type t = int * int

let dummy = (0,0)

let file = ref (None : string option)

let set_file f = file := Some f

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


