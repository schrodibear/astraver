
parameter x: int ref

let oppose = fun (u:unit) -> (x := - !x) { x = -x@ }

let test = 
  { x <= 10 }
  begin
    while !x < 10 do { invariant x <= 10 variant 10-x } x := !x + 1 done
    { x = 10 };
    (if !x > 0 then (oppose void)) 
    { x = -10 }
  end
