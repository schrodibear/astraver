
external x: int ref

let oppose =
  fun (u:unit) -> (x := - !x) { x = -x@ }

let test = 
   begin
     if !x < 0 then (oppose void)
   end
  { x >= 0 }
