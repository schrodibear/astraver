(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_why. Require Export caduceus_tactics.

(*Why*) Parameter copy_parameter :
  forall (t1: pointer), forall (t2: pointer), forall (n: Z),
  forall (alloc: alloc), forall (intP: ((memory) Z)),
  forall (H: ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n)) /\
  ~((base_addr t1) = (base_addr t2))),
  (sig_2 ((memory) Z) unit
   (fun (intP0: ((memory) Z)) (result: unit)  =>
    ((forall (k:Z),
      (0 <= k /\ k < n -> (acc intP0 (shift t2 k)) = (acc intP0 (shift t1 k))))))).

