
external visible : 
  x:int -> { x > 0 } returns result:bool { q(result,x) }

external a : int

let p = if a > 0 && (visible a) then void




