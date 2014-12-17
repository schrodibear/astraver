type t =
  | Zero
  | One of int
  | Two of int * bool

let f x b = Two(x, b)

(*
Local Variables: 
compile-command: "unset LANG; make -C .. variant.gui"
End: 
*)
