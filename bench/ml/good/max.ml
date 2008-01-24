let max x y =
  if x >= y then x else y

(*@ function max x y:
  @ requires x >= 0 && y >= 0
  @ ensures \result >= x && \result >= y
  @ behavior positive:
  @   ensures \result >= 0 *)

(*
Local Variables: 
compile-command: "unset LANG; make max"
End: 
*)
