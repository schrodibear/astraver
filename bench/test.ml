
(* Test program *)

parameter x : int ref

let p = (if !x = 0 then x := 1 else x := 2) { x <> 0 }




