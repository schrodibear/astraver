
(*i $Id: loc.mli,v 1.3 2001-08-24 19:07:17 filliatr Exp $ i*)

(*s Error location. *)

type t = int * int

val dummy : t

val set_file : string -> unit

(*s Error reporting. *)

open Format

val report : formatter -> t -> unit
