type t = {
  foo: int;
  mutable bar: int;
}

(*@ type t:
  @   invariant plouf x =
  @     x.foo >= x.bar
  @   invariant zero { bar = x } =
  @     x >= 0
  @*)

(*
Local Variables: 
compile-command: "unset LANG; make -C .. inv.gui"
End: 
*)
