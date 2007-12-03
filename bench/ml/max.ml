let max x y =
  (*@ ensures \result >= x && \result >= y && (\result = x || \result = y) *)
  if x >= y then x else y

let test x =
  (*@ ensures \result >= 0 *)
  max x 0

(*
Local Variables: 
compile-command: "unset LANG; make max.jc"
End: 
*)
