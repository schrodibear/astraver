
(* Fast exponentiation, using X^2n = (X^n)^2 and X^(2n+1) = X.(X^n)^2 *)

parameter x : int

parameter n,m,y : int ref

external div2 : int -> int

external is_odd : n:int -> { } bool { if result then Zodd(n) else Zeven(n) }

let power1 =
  { n >= 0 }
  begin
    m := x; 
    y := 1;
    while !n > 0 do
      { invariant Zpower(x,n@init) = y * Zpower(m,n) and n >= 0
        variant n }
      if (is_odd !n) then y := !y * !m;
      m := !m * !m;
      n := (div2 !n)
    done
  end
  { y = Zpower(x,n@init) }

