
(* Test program *)

parameter x : int ref
external t1,t2 : bool
external v1,v2,N : int

let p =
  begin
    let k = ref N in
    while t1 do { invariant I1(x) variant x } x := v1 done;
    assert { A(x) };
    while t2 do { invariant I2(x) variant x } x := v2 done
  end
  { Q(x) }

(* parameter t : array 10 of int *)

(*
let rec f (x:int ref) : unit { variant x } = 
  { x = 0 } begin x := 1 end { x = 1 }
*)
