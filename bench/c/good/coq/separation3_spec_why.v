(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Caduceus.

(*Why predicate*) Definition separation_L_S  (l:pointer) (s0:pointer)
  (r:((memory) pointer)) (q:((memory) pointer)) (c:((memory) pointer))
  (b:((memory) pointer)) (alloc:alloc_table)
  := ~((base_addr l) = (base_addr s0)) /\
     (~((base_addr s0) = (base_addr (acc q l))) /\
     ~((base_addr s0) = (base_addr (acc r l)))) /\
     ~((base_addr l) = (base_addr (acc b s0))) /\
     ~((base_addr l) = (base_addr (acc c s0))).

