
(* Simple loop. 
 
   Decreases reference [x] down to [0].
   While not necessary to establish postcondition [x = 0] we add
   [x <= x@0] to the invariant to illustrate the use of labels. *)

external x : int ref

let p = 
  { x >= 0 }
  while !x > 0 do 
    { invariant 0 <= x <= x@0  variant x } 
    x := !x - 1 
  done 
  { x = 0 }

