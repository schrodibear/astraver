
external x: int ref

let test_let = 
   begin
   if !x < 0 then x := !x + 1;
   if !x > 1 then x := !x - 1
   end
  { Q(x) }
