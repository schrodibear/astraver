
pvs "q: [real,real,real -> bool]
  sqrt: [nonneg_real -> nonneg_real]"

external a,b,c : float ref

let p = 
  begin 
    a := 1.0;
    b := 2.0;
    c := 3.0
(***
    (if !a > 0.0 && (sqrt !a) = 2.0 then a := 0.0);
    (if !a > 1.0 && (sqrt !a) = 4.0 then a := 5.0)
***)
  end
  { q(a,b,c) }



