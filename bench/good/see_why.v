(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.


(* Why obligation from file "good/see.mlw", characters 230-241 *)
(*Why goal*) Lemma k_po_1 : 
  forall (b0: Z),
  forall (Post1: b0 = 1),
  forall (b3: Z),
  forall (aux_4: Z),
  forall (Post18: aux_4 = b3 /\ b3 = (1 - b0)),
  forall (b4: Z),
  forall (aux_2: Z),
  forall (Post20: aux_2 = b4 /\ b4 = (1 - b3)),
  forall (result0: Z),
  forall (Post7: result0 = (1 - aux_2)),
  (forall (result:Z),
   (result = (result0 + aux_4) ->
    (forall (result0:Z),
     (forall (b:Z),
      (result0 = b /\ b = (1 - b4) ->
       (forall (result1:Z),
        (result1 = (1 - result0) ->
         (forall (result0:Z),
          (forall (b0:Z),
           (result0 = b0 /\ b0 = (1 - b) ->
            (forall (result2:Z),
             (result2 = (result0 * result1) -> result = 0 /\ result2 = 1)))))))))))).
Proof.
intuition.
subst; ring.
Qed.

