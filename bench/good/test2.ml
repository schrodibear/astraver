
external x : int ref

let test2 = (if !x = 0 then x := 1) { x /= 0 }

