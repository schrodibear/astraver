(**************************************************************************)
(*                                                                        *)
(* Proof of the Quicksort Algorithm.                                      *)
(*                                                                        *)
(* Jean-Christophe Filliâtre (LRI, Université Paris Sud)                  *)
(* August 1998                                                            *)
(*                                                                        *)
(**************************************************************************)

(* The first part of the program that re-arrange elements in the array
   and returns the position of the "partition" is defined in the module
   [Partition_prog]. *)

(* The recursive part of the quicksort algorithm:
   a recursive function to sort between [g] and [d] *)

(***
let quick_rec =
  let rec quick_rec (t:array N of int)(l,r:int) : unit 
  { variant r-l for Zwf(-1) } =
    { 0 <= l and r < N as Pre }
    (if l < r then
       let p = (partition t l r) in
       begin
       	 (quick_rec t l (p-1));
	 (quick_rec t (p+1) r)
       end)
    { sorted_array(t, l, r) and sub_permut(l, r, t, t@) }
***)

external quick_rec : t:(array N of int) -> l:int -> r:int ->
                     { 0 <= l and r < N as Pre } unit writes t
                     { sorted_array(t, l, r) and sub_permut(l, r, t, t@) }

(* At last, the main program, which is just a call to [quick_rec] *)

let quicksort =
  fun (t:array N of int) ->
    (quick_rec t 0 (N-1))
    { sorted_array(t, 0, N-1) and permut(t, t@) }
