(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_why. Require Export caduceus_tactics.

(*Why*) Parameter array1_parameter :
  forall (tt: unit), forall (intP: ((memory) Z)), forall (alloc: alloc),
  forall (t: pointer), forall (H: (valid_index alloc t 2)),
  (sig_2 ((memory) Z) Z
   (fun (intP0: ((memory) Z)) (result: Z)  => (result = 1))).

(*Why*) Parameter f2_parameter :
  forall (x: pointer), forall (alloc: alloc), forall (intP: ((memory) Z)),
  forall (H: (valid alloc x)),
  (sig_2 ((memory) Z) Z
   (fun (intP0: ((memory) Z)) (result: Z)  => ((acc intP0 x) = 1 /\ result =
    1))).

(*Why*) Parameter f_parameter :
  forall (x: pointer), forall (alloc: alloc), forall (intP: ((memory) Z)),
  forall (H: (valid alloc x)),
  (sig_2 ((memory) Z) Z
   (fun (intP0: ((memory) Z)) (result: Z)  => ((acc intP0 x) = 1 /\ result =
    0))).

(*Why*) Parameter g2_parameter :
  forall (tt: unit), forall (alloc: alloc), forall (intP: ((memory) Z)),
  forall (r: pointer),
  (sig_3 ((memory) Z) pointer Z
   (fun (intP0: ((memory) Z)) (r0: pointer) (result: Z)  => ((acc intP0 r0) =
    1))).

(*Why*) Parameter g_parameter :
  forall (tt: unit), forall (alloc: alloc), forall (intP: ((memory) Z)),
  forall (r: pointer), forall (H: (valid alloc r)),
  (sig_2 ((memory) Z) Z
   (fun (intP0: ((memory) Z)) (result: Z)  => ((acc intP0 r) = 1))).

(*Why*) Parameter h_parameter :
  forall (tt: unit), forall (alloc: alloc), forall (intP: ((memory) Z)),
  (sig_2 ((memory) Z) Z
   (fun (intP0: ((memory) Z)) (result: Z)  => (result = 1))).

(*Why*) Parameter malloc_parameter :
  forall (_: Z), (sig_1 pointer (fun (result: pointer)  => (True))).

