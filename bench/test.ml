
(* Test program *)

external x : int ref

let p = { q(1) } (3 + begin x := 1; !x end) { q(x) }


