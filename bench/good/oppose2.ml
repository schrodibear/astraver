
external x: int ref

let oppose =
  fun (u:unit) -> (x := - !x) { x = -x@ }

let test = 
   begin
     (oppose void);
     (oppose void)
   end
  { x = x@ }
