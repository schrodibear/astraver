
(*s Error location. *)

type t = int * int

val dummy : t

val set_file : string -> unit

(*s Error reporting. *)

open Format

val report : formatter -> t -> unit
