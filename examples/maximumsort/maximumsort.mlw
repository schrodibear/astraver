
(* maxisort: Maximum sort *)

(* swapping two elements of an array *)
let swap (N:int)(t:array N of int)(i,j:int) =
  { 0 <= i < N and 0 <= j < N }
  (let v = t[i] in
   begin
     t[i] := t[j];
     t[j] := v
   end)
  { exchange(t,t@,i,j) }

(* Maximize(t,n,x,k) is
   forall i, k <= i <= n implies t[k]<= x *) 
logic Maximize: array int, int, int, int -> prop

(* returns the index of the maximum element of t[0..n] *)
let rec maximum (N:int)(t:array N of int)(n,k,i:int): int { variant k } =
  { 0 <= k <= i and i <= n and n < N and Maximize(t,n,t[i],k) }
  (if k=0
   then i
   else
    let nk=k-1
    in if t[nk]>t[i]
   then (maximum N t n nk nk)
   else (maximum N t n nk i))
  { 0 <= result <= n and Maximize(t,n,t[result],0) }

(* Maximum sort *)
let maxisort (N:int)(t:array N of int) =
  { 0 <= N }
  (let i = ref (N-1) in
    while !i >= 0 do
      { invariant 0 <= i+1 <= N
            and sorted_array(t,i+1,N-1) and permut(t,t@init) 
            and (i+1 < N -> Maximize(t,i,t[i+1],0))
        variant i+1 }
      (let r = (maximum N t !i !i !i) in (swap N t !i r));
      i:=!i-1
    done)
  { sorted_array(t,0,N-1) and permut(t,t@) } 
