(**********************************************************************)
(*                                                                    *)
(* FIND, an historical example.                                       *)
(*                                                                    *)
(* The proof of this program was originally done by C. A. R. Hoare    *)
(* and fully detailed in the following paper:                         *)
(*                                                                    *)
(* C. A. R. Hoare, "Proof of a Program: FIND", Communications of the  *)
(* ACM, 14(1), 39--45, January 1971.                                  *)
(*                                                                    *)
(**********************************************************************)
(* Jean-Christophe FILLIATRE, February 98                             *)
(**********************************************************************)

(* specification *)

external N : int
external f : int

logic found : array int -> prop
logic m_invariant : int,array int -> prop
logic n_invariant : int,array int -> prop
logic i_invariant : int,int,int,int,array int -> prop
logic j_invariant : int,int,int,int,array int -> prop
logic termination : int,int,int,int,int,array int -> prop

(* Implementation part *)

parameter A : array N+1 of int   (* the array *)

let find =
  let m = ref 1 in let n = ref N in
  while !m < !n do
    { invariant m_invariant(m,A) and n_invariant(n,A) and permut(A,A@init) 
             and 1 <= m and n <= N as Inv_mn
      variant n-m }
    let r = A[f] in let i = ref !m in let j = ref !n in 
    begin
      while !i <= !j do
        { invariant i_invariant(m,n,i,r,A) and j_invariant(m,n,j,r,A)
      	         and m_invariant(m,A) and n_invariant(n,A)
		 and 0 <= j and i <= N+1
		 and termination(i,j,m,n,r,A)
      	       	 and permut(A,A@init) as Inv_ij
          variant N+2+j-i }
        label L;

        while A[!i] < r do
          { invariant i_invariant(m, n, i, r, A) 
      	       	   and i@L <= i and i <= n
		   and termination(i, j, m, n, r, A) as Inv_i
      	    variant N+1-i }
          i := !i + 1
        done;
      	
        while r < A[!j] do
          { invariant j_invariant(m, n, j, r, A) 
      	       	   and j <= j@L and m <= j
		   and termination(i, j, m, n, r, A) as Inv_j
            variant j }
       	  j := !j - 1
        done;

        assert { A[j] <= r and r <= A[i] };

        if !i <= !j then begin
          let w = A[!i] in begin A[!i] := A[!j]; A[!j] := w end;
	  assert { exchange(A, A@L, i, j) };
	  assert { A[i] <= r }; assert { r <= A[j] };
	  i := !i + 1;
	  j := !j - 1
        end
      done;

      assert { m < i and j < n };

      if f <= !j then
        n := !j
      else if !i <= f then
        m := !i
      else
        begin n := f; m := f end
    end
  done
  { found(A) and permut(A,A@init) }
