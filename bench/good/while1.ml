
parameter i : int ref

let p = 
  { i <= 10 }
  while !i < 10 do
    { invariant i <= 10 variant 10-i }
    i := !i + 1
  done
  { i = 10 }
