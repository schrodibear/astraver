
(* Test program *)

external x : int ref

let p = begin x := 1; (x := !x +1) { x = 2 }; x := !x + 1 end { x = 3 }

