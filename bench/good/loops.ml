
(** 1. A loop increasing [i] up to 10. *)

parameter i : int ref

let loop1 = 
  { i <= 10 }
  while !i < 10 do
    { invariant i <= 10 variant 10-i }
    i := !i + 1
  done
  { i = 10 }


(** 2. The same loop, followed by a function call. *)

parameter x: int ref

let oppose = fun (u:unit) -> (x := - !x) { x = -x@ }

let loop2 = 
  { x <= 10 }
  begin
    while !x < 10 do { invariant x <= 10 variant 10-x } x := !x + 1 done
    { x = 10 };
    (if !x > 0 then (oppose void)) 
    { x = -10 }
  end
