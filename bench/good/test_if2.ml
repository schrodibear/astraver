
external x,y : int ref

let p = 
  begin
    if !x > 0 then x := !x - 1 else x := !x + 1;
    if !y > 0 then y := !y - 1 else y := !y + 1
  end
  { q(x,y) }


