
parameter n : int
parameter t : array n of int

let selection =
  { n >= 1 }
  begin
    let i = ref 0 in
    while !i < n-1 do
      { invariant 0 <= i <= n-1 and
	          sorted_array(t, 0, i-1) and permut(t, t@init) and
	          forall k:int. 0 <= k < i ->
		    forall l:int. i <= l < n -> t[k] <= t[l]
	variant n - i }
      let min = ref !i in 
      let j = ref !i + 1 in
      begin
	while !j < n do
	  { invariant i+1 <= j <= n and i <= min < n and
	              forall k:int. i <= k < j -> t[min] <= t[k]
            variant n - j }
	  if t[!j] < t[!min] then min := !j;
	  j := !j + 1
	done;
	let w = t[!min] in begin t[!min] := t[!i]; t[!i] := w end
      end;
      i := !i + 1
    done
  end
  { sorted_array(t, 0, n-1) and permut(t, t@) }
