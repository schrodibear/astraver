
(* A variant of quicksort, with partitioning a la Bentley *)

parameter N : int

(* exchange of two elements *)

let swap (t:array N of int)(i,j:int) =
  { 0 <= i < N and 0 <= j < N }
  (let v = t[i] in
   begin
     t[i] := t[j];
     t[j] := v
   end)
  { exchange(t, t@, i, j) }

(* The recursive part of the quicksort algorithm:
   a recursive function to sort between [l] and [r] *)

let rec quick_rec (t:array N of int) (l,r:int) : unit { variant 1+r-l } =
  { 0 <= l and r < N (*as Pre*) }
  (if l < r then 
     let v = t[l] in
     let m = ref l in
     let i = ref (l + 1) in
     begin
       label L;
       while !i <= r do
	 { invariant (forall j:int. l < j <= m -> t[j] < v)
                 and (forall j:int. m < j <  i -> t[j] >= v)
                 and sub_permut(l, r, t, t@L)
                 and t[l] = v and l <= m < i and i <= r + 1
           variant 1 + r - i }
         if t[!i] < v then begin m := !m + 1; (swap t !i !m) end;
         i := !i + 1
       done;
       (swap t l !m);
       (quick_rec t l (!m - 1));
       (quick_rec t (!m + 1) r)
     end)
  { sorted_array(t, l, r) and sub_permut(l, r, t, t@) }

(* At last, the main program, which is just a call to [quick_rec] *)

let quicksort (t:array N of int) =
  (quick_rec t 0 (N-1))
  { sorted_array(t, 0, N-1) and permut(t, t@) }
