
external visible : 
  (x:int) returns result:bool pre x > 0 post q(result,x) end

external a : int

let p = if a > 0 && (visible a) then skip




