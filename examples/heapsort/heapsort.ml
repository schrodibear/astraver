
external Zdiv2 : int -> int

let heapsort =
  fun (N:int)(t:array N of int) ->
    { 1 <= N }
    begin
     (let k = ref (Zdiv2 (N-2)) in
      while !k >= 0 do
        { invariant -1 <= k <= N-1 
                 and (forall i:int. k+1 <= i <= N-1 -> heap(t, N-1, i))
		 and permut(t, t@init)
          variant k+1 }
      	(downheap N t !k (N-1));
	k := !k-1
      done)
      { heap(t, N-1, 0) and permut(t, t@init) };
      let k = ref (N-1) in
      while !k >= 1 do
        { invariant 0 <= k <= N-1 
                 and (forall i:int. 0 <= i <= k -> heap(t, k, i))
		 and (k+1 <= N-1 -> t[0] <= t[k+1])
		 and (k+1 <= N-1 -> sorted_array(t, k+1, N-1))
		 and permut(t, t@init)	
          variant k }
        (swap N t 0 !k);
        (downheap N t 0 (!k-1));
	k := !k-1
      done
    end
    { sorted_array(t, 0, N-1) and permut(t, t@) }
