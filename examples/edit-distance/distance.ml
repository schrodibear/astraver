
(*s Correctness of a program computing the minimal distance between two
    words (code by Claude Marché). *)

(*s Parameters. Input of the program is composed of two arrays
    of characters, [w1] of size [n1] and [w2] of size [n2]. *)

parameter n1 : int

parameter n2 : int

parameter w1 : array n1 of A
parameter w2 : array n2 of A

(*s Global variables of the program. The program uses an auxiliary
    array [t] of integers of size [n2+1] and three auxiliary
    integer variables [i], [j] and [old]. *)

parameter t : array n2+1 of int

parameter i,j,old : int ref

(*s Auxiliary definitions for the program and its specification. *)

external test_char : a:A -> b:A -> {} bool { if result then a=b else not a=b }

external Zmin : int -> int -> int

(*s The program and its proof of correctness. *)

let distance =
  begin
    (* initialization of t *)
      i := 0;
      while !i <= n2 do
        { invariant 0 <= i <= n2+1
                and forall j:int. 0 <= j < i -> t[j] = n2-j
          variant n2+1-i }
        t[!i] := n2 - !i;
        i := !i + 1
      done;
    (* loop over w1 *)
      i := n1 - 1;
      while !i >= 0 do
        { invariant -1 <= i <= n1-1
                and forall j:int. 0 <= j <= n2 -> min_suffix(w1,w2,i+1,j,t[j])
          variant i+1 }
        old := t[n2];
        t[n2] := t[n2] + 1;
        (* loop over w2 *)
        j := n2-1;
        while !j >= 0 do
          { invariant -1 <= j <= n2-1
                and (forall k:int. j < k <= n2 -> min_suffix(w1,w2,i,k,t[k]))
                and (forall k:int. 0 <= k <= j -> min_suffix(w1,w2,i+1,k,t[k]))
                and min_suffix(w1,w2,i+1,j+1,old)
	    variant j+1 }
	 (let temp = !old in
          begin
            old := t[!j];
	    if (test_char w1[!i] w2[!j]) then
	      t[!j] := temp
	    else
	      t[!j] := (Zmin t[!j] t[!j+1]) + 1
          end)
(***
          {    ((k:Z)j-1 < k <= n2 -> (min_suffix w1 w2 i k t[k]))
           and ((k:Z)0 <= k <= j-1 -> (min_suffix w1 w2 (i+1) k t[k]))
           and (min_suffix w1 w2 (i+1) (j-1+1) old) }
***)
;
          j := !j - 1
        done
(***
        { -1 <= i-1 <= n1-1
         and (j:Z)0 <= j <= n2 -> (min_suffix w1 w2 i j t[j]) }
***)
;
	i := !i - 1
      done;
      t[0]
  end
  { min_dist(word_of_array(w1), word_of_array(w2), result) }
