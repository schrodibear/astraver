
external x : int ref

let test6 = 
  begin x := !x + 1; label L; x := !x + 2 ; assert { x@L = x@0 + 1 } end 
  { x = x@ + 3 }



