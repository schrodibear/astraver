(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Caduceus.

(*Why logic*) Definition sum :
  alloc_table -> ((memory) Z) -> pointer -> Z -> Z -> Z.
Admitted.

(*Why axiom*) Lemma sum1 :
  (forall (alloc:alloc_table),
   (forall (intP:((memory) Z)),
    (forall (t:pointer), (forall (i:Z), (sum alloc intP t i i) = 0)))).
Admitted.

