(* expression *)
let g (x: int) = Array.make 42 x, 0

(* statement *)
let f (x: int) = Array.make 42 x

(*
Local Variables: 
compile-command: "unset LANG; make -C .. array_make.gui"
End: 
*)

