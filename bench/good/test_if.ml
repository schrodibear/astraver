
external x : int ref

let p = (if !x > 0 then x := !x - 1 else x := !x + 1) { q(x) }

