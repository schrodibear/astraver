
(* Test program *)

let f = fun (x:int) -> { x > 0 } x { x > 0 }

external r : int ref

let g = begin r := (f 1); r := !r + (f (f 2)) end
