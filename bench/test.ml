
(* Test program *)

external f : x:int -> y:int -> z:int -> { Pf(x,y,z) } unit { }

let p =
  fun (x:int) (y:int) (z:int) ->
    { P(x,y,z) }
    begin
      (f (x+y) z z)
    end
    { Q }
