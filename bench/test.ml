
(* Test program *)

external r : int ref

let p = (if true then begin r := 2; r := 1 end else r := 2) { r = 1 }

(** let p = begin r := 2; r := !r end { r = 2 } **)

(** let p = begin r := 1; r := !r end { r >= 0 } **)

(** let f = fun (x:int) -> { x > 0 } x { x > 0 } **)

(** let f = fun (x:int) -> { x > 0 } x { result = x } **)

(** external f : x:int -> { x > 0 } int { result = x } **)
