
external x: int ref

external f: (x:int)(y:bool)int

let test = 
  begin
    x := (f !x true)
  end


