
(* Peano_like arithmetic with references. *)

(* [add1 x y] adds [y] to [x], modifying [x] *)

let add1 = fun (x:int ref) (y:int) ->
  { y >= 0 }
  (let z = ref y in
   while !z > 0 do
     { invariant 0 <= z and x = x@0 + (y - z)
       variant z }
     x := !x + 1;
     z := !z - 1
   done)
  { x = x@ + y }

(* [mult1 x y] muliplies [x] by [y], modifiying [x] *)

(*
let mult1 = fun (x:int ref) (y:int) ->
*)
  
