
(* Test program *)

external r,s : int ref

let f = fun (x:int) -> { x > 0 } (r := !r + x) { r = r@ + x }

let u = (f 1)

let p = (f begin s := 2; 1 end) (* BUG: x pas substitué dans post résultat *)

