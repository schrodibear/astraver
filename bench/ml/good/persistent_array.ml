type t = {
  mutable data: data;
}

and data =
  | A of int array
  | D of int * int * t

let create n v = A(Array.make n v)

let rec get i t =
  match t.data with
    | A a -> a.(i)
    | D(j, v, t') -> if i = j then v else get i t'

let set i v t =
  match t.data with
    | A a ->
	let r = { data = A a } in
	t.data <- D(i, a.(i), r);
	a.(i) <- v;
	r
    | D _ ->
	{ data = D(i, v, t) }

(*
Local Variables: 
compile-command: "unset LANG; make -C .. persistent_array.gui"
End: 
*)
