type int_ref = {
  mutable contents: int;
}

let f x =
  while x.contents > 0 do
  (*@ invariant x.contents = \old x.contents @*)
    x.contents <- x.contents + 2;
    x.contents <- x.contents - 2;
  done;
  x.contents

(*
Local Variables: 
compile-command: "unset LANG; make -C .. while.gui"
End: 
*)
