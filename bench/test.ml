
(* Test program *)

parameter x : int ref

parameter t : array 10 of int

let u = let v = begin x := 0; !x end { result=0 } in t[v]

let p = (t[begin x := 0; !x end { result=0 }] := !x) { t[0] = x@ }

