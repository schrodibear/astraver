(**************************************************************************)
(*                                                                        *)
(* Proof of the Knuth-Morris-Pratt Algorithm.                             *)
(*                                                                        *)
(* Jean-Christophe Filli�tre (LRI, Universit� Paris Sud)                  *)
(* November 1998                                                          *)
(*                                                                        *)
(**************************************************************************)

external A_eq_bool : x:A -> y:A -> {} bool { if result then x=y else not x=y }

(* The pattern p is an array of length M. *)

parameter M : int

parameter p : array M of A

(* We first compute a global table next with the procedure initnext.
 * That table only depends on p. *)

parameter next : array M of int

let initnext =
  fun (u:unit) ->
   (let i = ref 1 in
    let j = ref 0 in
    if 1 < M then begin
      next[1] := 0;
      while !i < M-1 do
        { invariant 0 <= j <= M  and  j < i <= M
            and match(p, i-j, p, 0, j)
  	    and (forall z:int. j+1 < z < i+1 -> not match(p, i+1-z, p, 0, z))
            and (forall k:int. 0 < k <= i -> Next(p, k, next[k]))     as Inv
          variant pairZ(M-i, j) : prodZZ for lexZ }
        if (A_eq_bool p[!i] p[!j]) then begin
          i := !i+1; j := !j+1; next[!i] := !j
        end else
          if !j = 0 then begin i := !i+1; next[!i] := 0 end else j := next[!j]
      done
    end)
   { forall j:int. 0 < j < M -> Next(p, j, next[j]) }


(* The algorithm looks for an occurrence of the pattern p in a text a 
 * which is an array of length N. 
 * The function kmp returns an index i within 0..N-1 if there is an occurrence
 * at the position i and N otherwise. *)
  
parameter N : int

parameter a : array N of A

let kmp =
 (let i = ref 0 in
  let j = ref 0 in
  begin
    (initnext void);
    while !j < M && !i < N do
      { invariant 0 <= j <= M and j <= i <= N
           and match(a, i-j, p, 0, j)
           and forall k:int. 0 <= k < i-j -> not match(a, k, p, 0, M) as Inv
        variant pairZ(N-i, j) : prodZZ for lexZ }
      if (A_eq_bool a[!i] p[!j]) then begin
        i := !i+1; j := !j+1
      end else
        if !j = 0 then i := !i+1 else j := next[!j]
    done;	
    if !j = M then !i-M else !i
  end)
  { first_occur(p, a, result) }
