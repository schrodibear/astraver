
exception Return of int

parameter N : int

parameter i : int ref
parameter t : array N of int

let p = 
  try begin
    i := 0;
    while !i < N do
      { invariant 0 <= i (* and forall k:int. 0 <= k < i => t[k] <> 0 *)
        variant N - i }							 
      if t[!i] = 0 then raise (Return !i);
      i := !i + 1
    done;
    N
  end with Return x ->
    x
  end
  { 0 <= result < N -> t[result] = 0 }

