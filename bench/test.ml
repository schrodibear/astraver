
(* Test program *)

parameter x : int ref

parameter t : array 10 of int

let p = (t[begin x := 0; !x end] := !x) { t[0] = x@ }

(*
let rec f (x:int) : unit { variant x } = 
  { x >= 0 } if x > 0 then (f (x-1)) else void
*)

