type t = A of int | B of int * (int * bool)

let f x = match x with
  | A i
  | B(42, (i, _))
  | B(69, (i, _)) -> i
  | B(_, (i, _)) -> i

(*
Local Variables: 
compile-command: "unset LANG; make match"
End: 
*)
