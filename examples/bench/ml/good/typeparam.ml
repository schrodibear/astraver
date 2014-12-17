type ('a, 'b, 'c) ref3 = {
  contents3: 'a;
  contents4: 'b;
  contents5: 'c;
}

let f (x: int) = {
  contents3 = x;
  contents4 = 1 >= 2;
  contents5 = 5.;
}

let g (x: bool) = {
  contents3 = x;
  contents4 = 1.;
  contents5 = 5;
}

type ('a, 'b, 'c) plop =
  | Plop of 'a * int
  | Plouf of 'b * 'c

(*let h (x: bool) = Plop(x, 1)*)

let h (x: bool) = (Plop(x, 1): (bool, int, float) plop)

let i (x: bool) = (Plop(x, 1): (bool, int, int) plop)

(*
Local Variables: 
compile-command: "unset LANG; make -C .. typeparam.gui"
End: 
*)
