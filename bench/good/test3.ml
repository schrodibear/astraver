
external x : int ref

let test3 = (if !x = 0 then x := !x + 1) { x <> 0 }

