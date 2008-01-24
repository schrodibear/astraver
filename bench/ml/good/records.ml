type test = {
  foo: int;
  mutable bar: int;
}

let yop x =
  let r = { foo = 42; bar = x.foo } in
  r.bar <- x.bar

let plop y x =
  if y then
    x.bar <- x.foo
  else
    x.bar <- 0

(*
Local Variables: 
compile-command: "unset LANG; make records"
End: 
*)
