(**************************************************************************)
(*                                                                        *)
(* Proof of the Quicksort Algorithm.                                      *)
(*                                                                        *)
(*  This formal proof is detailed in this paper:                          *)
(*                                                                        *)
(*  J.-C. Filli�tre and N. Magaud. Certification of sorting algorithms    *)
(*  in  the system  Coq. In  Theorem Proving  in Higher  Order Logics:    *)
(*  Emerging Trends, 1999.                                                *)
(*  (http://www.lri.fr/~filliatr/ftp/publis/Filliatre-Magaud.ps.gz)       *)
(*                                                                        *)
(* Jean-Christophe Filli�tre (LRI, Universit� Paris Sud)                  *)
(* August 1998                                                            *)
(*                                                                        *)
(**************************************************************************)

(* The first part of the program that re-arrange elements in the array
   and returns the position of the "partition" is defined in the module
   [Partition_prog]. *)

(* The recursive part of the quicksort algorithm:
   a recursive function to sort between [g] and [d] *)

let quick_rec =
  let rec quick_rec (t:array N of int)(l,r:int) : unit 
  { variant 1+r-l } =
    { 0 <= l and r < N (*as Pre*) }
    (if l < r then
       let p = (partition t l r) in
       begin
       	 (quick_rec t l (p-1));
	 (quick_rec t (p+1) r)
       end)
    { sorted_array(t, l, r) and sub_permut(l, r, t, t@) }

(* At last, the main program, which is just a call to [quick_rec] *)

let quicksort =
  fun (t:array N of int) ->
    (quick_rec t 0 (N-1))
    { sorted_array(t, 0, N-1) and permut(t, t@) }
