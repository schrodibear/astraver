(**************************************************************************)
(*                                                                        *)
(* Proof of the Quicksort Algorithm.                                      *)
(*                                                                        *)
(*  This formal proof is detailed in this paper:                          *)
(*                                                                        *)
(*  J.-C. Filliâtre and N. Magaud. Certification of sorting algorithms    *)
(*  in  the system  Coq. In  Theorem Proving  in Higher  Order Logics:    *)
(*  Emerging Trends, 1999.                                                *)
(*  (http://www.lri.fr/~filliatr/ftp/publis/Filliatre-Magaud.ps.gz)       *)
(*                                                                        *)
(* Jean-Christophe Filliâtre (LRI, Université Paris Sud)                  *)
(* August 1998                                                            *)
(*                                                                        *)
(**************************************************************************)

parameter N : int

(* exchange of two elements *)

let swap =
  fun (t:array N of int)(i,j:int) ->
    { 0 <= i < N and 0 <= j < N }
    (let v = t[i] in
     begin
       t[i] := t[j];
       t[j] := v
     end)
    { exchange(t, t@, i, j) }

(* partition *)

logic partition_p : array int, int, int, int -> prop

let partition =
  fun (t:array N of int)(l,r:int) ->
    { 0 <= l < r and r < N }
   (let pv = t[l] in
    let i = ref (l+1) in
    let j = ref r in
    begin
      while !i < !j do
      	{ invariant l+1 <= i <= r and j <= r
                 and array_le(t, l+1, i-1, pv)
		 and array_ge(t, j+1, r, pv)
		 and sub_permut(l, r, t, t@init)
                 and t[l]=t@init[l] as Inv
          variant N+2+j-i }
        label L;
	while t[!i] <= pv && !i < !j do
      	  { invariant i@L <= i <= r and array_le(t, l+1, i-1, pv) as Invi
            variant r-i }
	  i := !i + 1
	done;
	while t[!j] >= pv && !i < !j do
	  { invariant l <= j <= j@L and array_ge(t, j+1, r, pv) as Invj
            variant j }
	  j := !j - 1
	done;
	if !i < !j then begin
      	  (swap t !i !j);
	  i := !i + 1;
	  j := !j - 1
	end
      done;
      (if t[!i] < pv then begin
      	 (swap t l !i);
         !i
       end else begin
      	 (swap t l (!i - 1));
      	 !i - 1
       end) 
    end)
    { l <= result <= r and 
      partition_p(t, l, r, result) and sub_permut(l, r, t, t@) }

