type t = A of int | B of int * int

let f x = match x with
  | A i
  | B(42, i)
  | B(69, i) -> i
  | B(_, i) -> i

(*
Local Variables: 
compile-command: "unset LANG; make match"
End: 
*)
