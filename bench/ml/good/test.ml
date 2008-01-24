let f x y z =
  if x then y else z

let g x y =
  x; y

let h (x: int) y =
  (let z = x in z); y

let i x y z =
  if (let z = x in z) then y else z

let j x y z t (u: int) =
  if (if x then y else z) then t else u

(*
Local Variables: 
compile-command: "unset LANG; make -C .. test.gui"
End: 
*)
