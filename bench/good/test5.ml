
external x : int ref

let test5 = begin x := !x + 1; x := !x + 2 end { x > x@ }



