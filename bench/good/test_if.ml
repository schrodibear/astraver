
external x : int ref

let p = { x <> 0 }
        (if !x > 0 then x := !x - 1 else x := !x + 1) 
        { Zabs(x) < Zabs(x@) }

