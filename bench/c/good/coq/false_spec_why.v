(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Caduceus.

(*Why predicate*) Definition separation_int_int  (y_0:pointer) (x_0:pointer)
  := ~((base_addr y_0) = (base_addr x_0)).

(*Why predicate*) Definition separation_int_u  (x_0:pointer) (zz:pointer)
  := ~((base_addr x_0) = (base_addr zz)).

