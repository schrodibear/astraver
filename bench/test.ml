
(* Test program *)

external r : int ref

(** let p = begin r := 1; r := !r end { r >= 0 } **)

(** let f = fun (x:int) -> { x > 0 } x { x > 0 } **)

(** let f = fun (x:int) -> { x > 0 } x { result > 0 } **)
external f : x:int -> { x > 0 } int { result > 0 }

let g = r := (f (f 2))
