(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Caduceus.

(*Why type*) Definition global: Set.
Admitted.

(*Why predicate*) Definition purse_inv  (balance_global:((memory) Z global))
  (alloc:alloc_table) (p:((pointer) global))
  := (* File "purse.c", line 6, characters 37-65 *) ((valid alloc p) /\
     (acc balance_global p) >= 0).

