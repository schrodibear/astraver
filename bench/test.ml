
(* Test program *)

external x : int ref
external t : array 10 of int

let p = (t[begin t[0] := 3; 4 end] := begin t[4] := 0; 1 end) 
        { access(t,4) = 1 }

(***

external t : array 10 of int

(*** BUG capture global/local ***)

external x : int ref

let f = fun (u:unit) -> x := 0

let g = fun (x:int ref) -> begin (f void); x := 1 end

(****)

let f = fun (a,b,c:int ref) -> 
  { a = 0 and b = 0 and c = 0 }
  begin a := 1; b := 2; c := 3 end
  { a = 1 and b = 2 and c = 3 }

external x,y,z: int ref

let g = (f x)

let p = (g y z) { z = 3 }

let p2 = (g z y) { y = 3 }

(****
external r,s : int ref

let f = fun (x:int) -> 
  { x > 0 } begin r := !r + x; s := 0 end { r = r@ + x and s = 0 }

let p = (f begin s := 2; 1 end { result = 1 }) { s = 0 }
****)

***)
