(* This file is generated by Why; do not edit *)

Require Why.
Require Export oldify_why.

Definition g1 (* validation *)
  : (r: Z)(sig_2 Z unit [r0: Z][result: unit]((q1 r0 r r)))
  := [r: Z]
       let (r0, result1, Post1) = (f1 r r) in
       (exist_2 [r1: Z][result2: unit](q1 r1 r r) r0 result1 Post1).

Definition g (* validation *)
  : (t: (array Z))
    (sig_2 (array Z) unit [t0: (array Z)][result: unit]
     ((q t0 t (array_length t))))
  := [t: (array Z)]
       let (t0, result1, Post1) = (f (array_length t) t) in
       (exist_2 [t1: (array Z)][result2: unit](q t1 t (array_length t)) 
       t0 result1 Post1).

