
external N : int
external v : int

external mean : int -> int -> int

external t : array (N+1) of int

external l,u,p,m : int ref

let binary_search =
  { sorted_array(t,1,N) }
  begin
    l := 1; u := N; p := 0;
    while !l <= !u do
      { invariant 1 <= l and u <= N and 0 <= p and p <= N
               and (p = 0 -> In(t,1,N) -> In(t,l,u))
               and (p > 0 -> access(t,p)=v)
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
  { (1 <= p and p <= N and access(t,p)=v) or (p = 0 and not In(t,1,N)) }

