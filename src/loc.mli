
(*i $Id: loc.mli,v 1.4 2002-03-01 16:29:49 filliatr Exp $ i*)

(*s Error location. *)

type t = int * int

val dummy : t

val join : t -> t -> t

val set_file : string -> unit

(*s Error reporting. *)

open Format

val report : formatter -> t -> unit
