
let p = 0 = 1

external x: int ref

external f: (x:(u:int)int)(y:bool)int

let test = 
  begin
    x := (f !x true)
  end


