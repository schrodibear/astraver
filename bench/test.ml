
external N : int
external f : int

logic Iloopmn : int,int,array int -> prop
logic Iloopij : int,int,int,int,int,array int -> prop
logic Iloopi : int,int,int,int,int,array int -> prop
logic Iloopj : int,int,int,int,int,array int -> prop
logic q : array int, array int -> prop

parameter A : array N+1 of int 

parameter m,i,j,n : int ref
parameter r : int

let find =
  while true do
    {  variant n }
      A[1] := 2
  done
  { q(A,A@) }


(*****
let find =
  let m = ref 1 in let n = ref N in
  while !m < !n do
    { invariant Iloopmn(m,n,A) variant n-m }
    let r = A[f] in let i = ref !m in let j = ref !n in 
    begin
      while !i <= !j do
        { invariant Iloopij(m,n,i,j,r,A)  variant N+2+j-i }
        label L;
(***
        while A[!i] < r do
          { invariant Iloopi(m,n,i,j,r,A)  variant N+1-i }
          i := !i + 1
        done;
      	
        while r < A[!j] do
          { invariant Iloopj(m,n,i,j,r,A)  variant j }
       	  j := !j - 1
        done;
***)

        assert { A[j] <= r and r <= A[i] };

        if !i <= !j then begin
          let w = A[!i] in begin A[!i] := A[!j]; A[!j] := w end;
	  assert { exchange(A, A@L, i, j) };
	  assert { A[i] <= r }; assert { r <= A[j] };
	  i := !i + 1;
	  j := !j - 1
        end
      done

(***
      assert { m < i and j < n };

      if f <= !j then
        n := !j
      else if !i <= f then
        m := !i
      else
        begin n := f; m := f end
***)
    end
  done
  { q(A,A@) }
*****)
