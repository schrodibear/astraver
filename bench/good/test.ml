
external x: int ref

let oppose = fun (u:unit) -> (x := - !x) { x = -x@ }

let test = 
  { x <= 10 }
  begin
    while !x < 10 do { invariant x <= 10 variant 10-x } x := !x + 1 done;
    (oppose void)
  end
  { x = -10 }
