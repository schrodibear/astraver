
parameter N : int

parameter v : int

parameter t : array (N+1) of int

parameter l,u,p,m : int ref

external mean : int -> int -> int

let binary_search =
  { sorted_array(t,1,N) }
  begin
    l := 1; u := N; p := 0;
    while !l <= !u do
      { invariant 1 <= l and u <= N and 0 <= p <= N
               and (p = 0 -> In(t,1,N) -> In(t,l,u))
               and (p > 0 -> t[p]=v)
        variant 2+u-l }
      m := (mean !l !u);
      assert { l <= m and m <= u };
      if t[!m] < v then
        l := !m + 1
      else if t[!m] > v then
        u := !m - 1
      else begin
        p := !m; (* break => *) l := !u + 1
      end       
    done
  end
  { (1 <= p <= N and t[p]=v) or (p = 0 and not In(t,1,N)) }

