
(* Test program *)

(* parameter x : int ref *)

let rec f (x:int) : unit { variant x } = 
  { x >= 0 } if x > 0 then (f (x-1)) else void

