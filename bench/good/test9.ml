
external x : int ref

pvs "q: [int -> bool]"

(*
let p = (if !x > 0 && (2 / !x = 0) then x := 1) { q(x) }
*)

