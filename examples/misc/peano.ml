
(* Peano-like arithmetic with references. *)

(* [add1 x y] adds [y] to [x], modifying [x] *)

let add1 = fun (x:int ref) (y:int) ->
  { y >= 0 }
  (let z = ref y in
   while !z > 0 do
     { invariant 0 <= z and x = x@init + (y - z) as I
       variant z }
     x := !x + 1;
     z := !z - 1
   done)
  { x = x@ + y }

(* test *)

let u1 = let r = ref 3 in (add1 r 7) { r = 10 }

(* recursive version *)

let rec rec_add1 (x:int ref) (y:int) : unit { variant y } =
  { y >= 0 }
  (if 0 < y then begin x := !x + 1; (rec_add1 x (y-1)) end)
  { x = x@ + y }

(* test *)

let u11 = let r = ref 3 in (rec_add1 r 7) { r = 10 }

(* [mult1 x y] muliplies [x] by [y], modifiying [x] *)

let mult1 = fun (x:int ref) (y:int) ->
  { x >= 0 and y >= 0 }
  (let z = ref y in
   let savex = !x in
   begin
     x := 0;
     while !z > 0 do
       { invariant 0 <= z and x = x@init * (y - z) as I
         variant z }
       (add1 x savex);
       z := !z - 1
     done
   end)
  { x = x@ * y }

(* test *)

let u2 = let r = ref 4 in (mult1 r 6) { r = 24 }
