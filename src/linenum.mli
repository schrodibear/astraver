
(* [from_char f n] gives the actual source file, line number, position of the
   beginning of the line. *)

val from_char : string -> int -> string * int * int
