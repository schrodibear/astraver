
(* Test program *)

external r : int ref

let p = (if !r = 1 || !r = 2 then r := 3) { r <> 1 and r <> 2 }

(** let p = begin r := 2; r := !r end { r = 2 } **)

(** let p = begin r := 1; r := !r end { r >= 0 } **)

(** let f = fun (x:int) -> { x > 0 } x { x > 0 } **)

(** let f = fun (x:int) -> { x > 0 } x { result = x } **)

(** external f : x:int -> { x > 0 } int { result = x } **)
