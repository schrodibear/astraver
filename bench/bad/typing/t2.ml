external x : int ref

let p = if begin x := 0; x := 0 end then x := 1


