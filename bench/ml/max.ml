let max x y
  (*@ behavior ok:
        ensures x && x
(*          && \result >= y && (\result = x || \result = y) *) *)
    =
  if x then y >= 0 else 0 >= y

(*let test x =
  (*@ ensures \result >= 0 *)
  max x 0*)

(*
Local Variables: 
compile-command: "unset LANG; make max.jc"
End: 
*)
