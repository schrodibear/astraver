let max x y =
  if x >= y then x else y

(*@ function max x y:
  @ requires x >= x
  @ ensures \result >= x && \result >= y
  @ behavior test:
  @   ensures \result >= \result *)

(*
Local Variables: 
compile-command: "unset LANG; make max.jc"
End: 
*)
