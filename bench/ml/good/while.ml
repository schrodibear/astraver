type int_ref = {
  mutable contents: int;
}

let double x =
  let tmp = { contents = x.contents } in
  let result = { contents = 0 } in
  assert (x <> result && tmp <> result && x <> tmp);
  while tmp.contents > 0 do
  (*@ variant tmp.contents
    @ invariant result.contents + 2 * tmp.contents = 2 * x.contents &&
    @   tmp.contents >= 0 && x.contents = \old x.contents
    @*)
    result.contents <- result.contents + 2;
    tmp.contents <- tmp.contents - 1;
  done;
  result.contents

(*@ function double x:
  @   requires x.contents >= 0
  @   ensures \result = x.contents * 2 &&
  @     x.contents = \old x.contents
  @*)

(*
Local Variables: 
compile-command: "unset LANG; make -C .. while.gui"
End: 
*)
