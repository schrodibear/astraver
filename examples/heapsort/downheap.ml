
(* The recursive function downheap *)

logic select_son : array int, int, int, int -> prop
logic inftree : array int, int, int, int -> prop
logic heap : array int, int, int -> prop 

let downheap = 
  let rec downheap (N:int)(t:array N of int)(k,n:int) : unit { variant n-k } =
  {     0 <= k <= n and n < N
    and forall i:int. k+1 <= i <= n -> heap(t, n, i) }
  (let j = 2*k+1 in
   if j <= n then
     let j' = (if j+1 <= n then if t[j] < t[j+1] then j+1 else j else j)
              { select_son(t, k, n, result) } 
     in
     if t[k] < t[j'] then begin (swap N t k j'); (downheap N t j' n) end)
  {     permut(t, t@)
    and (forall i:int. k <= i <= n -> heap(t, n, i))
    and (forall i:int. (0<=i<k or k<i<2*k+1 or n<i<N) -> t[i]=t@[i])
    and (forall v:int. inftree(t@, n, v, k) -> inftree(t, n, v, k)) }
