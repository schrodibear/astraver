(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Caduceus.

(*Why predicate*) Definition valid_dim2  (alloc:alloc_table)
  (intPP:((memory) pointer)) (t_0:pointer) (i:Z) (j:Z) (k:Z) (l:Z)
  := (* File \"array.c\", line 8, characters 7-86 *)
     ((valid_range alloc t_0 i j) /\
     (forall (n:Z),
      (i <= n /\ n <= j -> (valid_range alloc (acc intPP (shift t_0 n)) k l)))).
