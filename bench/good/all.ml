
(* The good file. All program constructions. *)

let p1 = 0

let p2 = (1 + 2) * 3

let p3 = 
  let x = ref 0 in
  (x := !x + 1) { x = 1 }

external x : int ref
external a : array 10 of float

let p4 = !x

external f : fun (a:int)(b:int ref) returns c:int
                                            reads x,b
					    writes b
					    pre a=0 and b=0
					    post b > 0 end
let p5 = { x = 0 } (f 0 x)

let p6 = 
  let x = ref 0 in
  begin
    x := !x + 1;
    x := !x + 2;
    assert { x = 3 };
    x := !x + 3
  end
  { x = 6 }

