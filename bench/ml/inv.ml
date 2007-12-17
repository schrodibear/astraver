type t = {
  foo: int;
  mutable bar: int;
}

type u =
  | A of int * bool
  | B

type v =
  | Zero
  | One of int
  | Two of int * bool
  | Three of u * u * u

(*@ type t:
  @   invariant plouf x =
  @     x.foo >= x.bar
  @   invariant zero { bar = x } =
  @     x >= 0
  @*)

(*@ type v:
  @   invariant plop (One x | Two(x, _)) = x >= 0
(*  @   invariant bla Three(A(_, x), A(_, y), B) = x = y*)
  @*)

(*
Local Variables: 
compile-command: "unset LANG; make inv"
End: 
*)
