(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require WhyFloat.


Lemma f_po_1 : 
  (y: Z)
  (ddd: Z)
  (z: Z)
  (Pre1: `y = ddd`)
  (result: Z)
  (Post3: result = z)
  (aux_1: Z)
  (Post2: aux_1 = result)
  (u0: Z)
  (Post1: u0 = `result + 1`)
  `aux_1 = z`.
Proof.
Intuition.
Save.

Lemma main_po_1 : 
  (x0: Z)
  (Post1: x0 = `0`)
  (x1: Z)
  (Post2: x1 = `x0 + 1`)
  ((result:Z) (`result = 2` -> `result = 2`)) /\ `1 = x1`.
Proof.
Intuition.
Save.

Lemma main_po_2 : 
  (x0: Z)
  (Post1: x0 = `0`)
  (aux_2: Z)
  (Post5: ((result:Z) (`result = 2` -> `result = 2`)) /\ `1 = aux_2`)
  `1 = aux_2`.
Proof.
Intuition.
Save.

