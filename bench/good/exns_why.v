(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.



(* Why obligation from file "good/exns.mlw", characters 838-845 *)
Lemma p7_po_1 : 
  (x0: Z)
  (Post1: x0 = `1`)
  `x0 = 1`.
Proof.
Intuition.
Save.


(* Why obligation from file "good/exns.mlw", characters 923-925 *)
Lemma p8_po_1 : 
  (x0: Z)
  (Post1: x0 = `1`)
  `x0 = 1` /\ `x0 = 1`.
Proof.
Intuition.
Save.


(* Why obligation from file "good/exns.mlw", characters 1020-1022 *)
Lemma p9_po_1 : 
  (x0: Z)
  (Post1: x0 = `1`)
  `x0 = 1` /\ `x0 = 1`.
Proof.
Intuition.
Save.









(* Why obligation from file "good/exns.mlw", characters 1372-1379 *)
Lemma p13_po_1 : 
  ((x:Z) (x = `2` -> `x = 2`)).
Proof.
Intuition.
Save.



(* Why obligation from file "good/exns.mlw", characters 1534-1557 *)
Lemma p14_po_1 : 
  (x: Z)
  (Test1: `x <> 1`)
  ((`x = 2` -> `x = 2`)) /\
  ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
    ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)))).
Proof.
Intuition.
Save.


