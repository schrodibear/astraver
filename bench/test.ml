
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



