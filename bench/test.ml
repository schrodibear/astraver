
(* Test program *)

let rec rec_add1 (x:int ref) (y:int) : unit { variant y } =
  { y >= 0 }
  (if 0 < y then begin x := !x + 1; (rec_add1 x (y-1)) end)
  { x = x@ + y }

(* test *)

let u11 = let r = ref 3 in (rec_add1 r 7) { r = 10 }

(***
external f : x:int -> y:int -> z:int -> { Pf(x,y,z) } unit { }

let p =
  fun (x:int) (y:int) (z:int) ->
    { P(x,y,z) }
    begin
      (f (x+y) z z)
    end
    { Q }
***)
