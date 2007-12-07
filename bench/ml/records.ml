type test = {
  foo: int;
  mutable bar: int;
}

let foo x =
  { foo = 42; bar = x.foo }.bar <- x.bar

(*
Local Variables: 
compile-command: "unset LANG; make records"
End: 
*)
