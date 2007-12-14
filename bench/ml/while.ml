type int_ref = {
  mutable contents: int;
}

let (!) x = x.contents

(*@ function (!) x:
  @   ensures \result = x.contents
  @*)

let (:=) x v = x.contents <- v

(*@ function (:=) x v:
  @   ensures x.contents = v
  @*)

let ref v = { contents = v }

(*@ function ref v:
  @   ensures \result.contents = v
  @*)

let double x =
  let result = { contents = 0 } in
  (*@ assert x <> result *)
  while !x >= 0 do
  (*@ variant x.contents
    @ invariant result.contents + 2 * x.contents = 2 * \old x.contents
    @*)
    result := !result + 2;
    x := !x - 1;
  done;
  !result

(*@ function double x:
  @   requires x.contents >= 0
  @   ensures \result = x.contents * 2
  @*)

(*
Local Variables: 
compile-command: "unset LANG; make while"
End: 
*)
