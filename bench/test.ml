
logic f : int -> int
logic p : int -> prop
logic c : -> int
logic A : -> prop

let test = void { f(1)=c and A and p(f(2)) }

(***
exception E

let p = raise E

let f (a_:int) (b_:int) = 
 (let a = ref a_ in
  let b = ref b_ in
  begin
    a := !a + !b;
    b := 0;
    !a
  end)
 { result = a_ + b_ }

***)



