
(* Test program *)

(* parameter x : int ref *)

parameter t : array 10 of int

let p = begin t[1+2] := 3+4; t[2] := 1 end { t[3] = 7 }

(*
let rec f (x:int) : unit { variant x } = 
  { x >= 0 } if x > 0 then (f (x-1)) else void
*)

