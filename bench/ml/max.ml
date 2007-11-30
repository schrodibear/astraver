let max x y =
  (*@ ensures \result >= x && \result >= y && (\result = x || \result = y) *)
  if x >= y then x else y

(*
Local Variables: 
compile-command: "unset LANG; make max.jc"
End: 
*)
