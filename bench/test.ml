
(* Test program *)

parameter x : int ref

parameter foo : int -> int

parameter N : int

let p = { q(1) } (3 + begin x := 1; !x end) { q(N) }


