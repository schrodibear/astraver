type test = {
  foo: int;
  mutable bar: int;
}

let foo x =
  let r = { foo = 42; bar = x.foo } in
  r.bar <- x.bar

(*
Local Variables: 
compile-command: "unset LANG; make records"
End: 
*)
