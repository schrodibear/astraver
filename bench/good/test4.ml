
external x : int ref

let test4 = (x := !x + 1) { x > x@ }


