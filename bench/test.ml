
(* Test program *)

external r,s : int ref

let f = fun (x:int) -> (r := !r + x) { r = r@ + x }

let p = (f begin s := 2; 1 end) (* BUG: x pas substitué dans post résultat *)

