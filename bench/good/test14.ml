
external a,b,c,d : int ref

let p =
  if !a = 0 then begin
    a := 1;
    b := 2;
    c := 3;
    (if !c = 0 then d := 1) { q(a,b,c,d) };
    if !b = 0 && !c = 0 then begin a := 4; c := 5 end
  end
  { q(a,b,c,d) }
    
