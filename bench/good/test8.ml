
external x : int ref

pvs "sqrt: [nonneg_real -> real]
  q: [real -> bool]"

(***
let test8b = 
  { x > 0 } 
  begin 
    x := sqrt !x;
    x := 4.0 / !x
    x := sqrt !x
  end 
  { q(x) }
***)


