(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.


(* Why obligation from file "good-c/call.c", characters 113-116 *)
Lemma f_po_1 : 
  (y: Z)
  (ddd: Z)
  (z: Z)
  (Pre1: `y = ddd`)
  (result: Z)
  (Post3: result = z)
  (c_aux_1: Z)
  (Post2: c_aux_1 = result)
  (u0: Z)
  (Post1: u0 = `result + 1`)
  `c_aux_1 = z`.
Proof.
Intuition.
Save.


(* Why obligation from file "good-c/call.c", characters 174-177 *)
Lemma main_po_1 : 
  (x0: Z)
  (Post1: x0 = `0`)
  (x1: Z)
  (Post2: x1 = `x0 + 1`)
  ((result:Z) (`result = 2` -> `result = 2`)) /\ `1 = x1`.
Proof.
Intuition.
Save.


