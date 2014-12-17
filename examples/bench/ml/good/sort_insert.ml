type 'a mylist = N | C of 'a * 'a mylist

(*@ predicate mysorted (l: int mylist) reads l *)

(*@ logic type myset *)

(*@ logic function mycontents (l: int mylist): myset reads l *)

(*@ logic function myadd (x: int) (s: myset): myset reads x, s *)

(*@ axiom mysorted_sub (C(_, l2) as l1) = mysorted l1 ==> mysorted l2 *)

(*@ axiom mysorted_singleton (C(x, (N as empty)) as l) = mysorted l &&
  @   mycontents l = myadd x (mycontents empty) *)

(*@ axiom mysorted_cons_inf (C(x, (C(hd, _) as l1)) as l2) =
  @   x <= hd ==> mysorted l1 ==> mysorted l2
  @*)

(*@ axiom mysorted_cons_sup (C(x, (C(hd, rem) as l1)) as l2) xrem
  @     (C(a, b) as l3) =
  @   x > hd ==>
  @   mysorted xrem ==> mycontents xrem = myadd x (mycontents rem) ==>
  @   a = hd ==> b = xrem ==>
  @   mysorted l3 && mycontents l3 = myadd x (mycontents l1)
  @*)

let rec insert x l = match l with
  | N -> C(x, N)
  | C(hd, rem) -> if x <= hd then C(x, l) else C(hd, insert x rem)

(*@ function insert x l:
  @   requires mysorted l
  @   ensures mysorted \result && mycontents \result = myadd x (mycontents l)
  @*)

let rec sort l = match l with
  | N -> N
  | C(hd, rem) -> insert hd (sort rem)

(*@ function sort l:
  @   ensures mysorted \result && mycontents \result = mycontents l
  @*)

(*
Local Variables: 
compile-command: "unset LANG; make -C .. sort_insert.gui"
End: 
*)
