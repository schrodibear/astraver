
external a : int ref

let p =
  begin
    if !a = 0 then a := 1;
    if !a = 2 then a := 3
  end
  { q(a) }
