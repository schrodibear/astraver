
Require Import Why.

(*Why logic*) Definition q1 : Z -> Z -> Z -> Prop.
Admitted.







(*Why logic*) Definition q : (array Z) -> (array Z) -> Z -> Prop.
Admitted.





(* Why obligation from file "good/oldify.mlw", line 17, characters 2-82: *)
(*Why goal*) Lemma g_po_1 : 
  (* File "good/oldify.mlw", line 17, characters 1-81 *)
  (forall (t:(array Z)),
   (* File "good/oldify.mlw", line 18, characters 9-24 *)
   (forall (result:Z),
    ((* File "good/oldify.mlw", line 18, characters 9-24 *) result =
     (array_length t) ->
     (* File "good/oldify.mlw", line 18, characters 4-25 *)
     (forall (t0:(array Z)),
      ((* File "good/oldify.mlw", line 18, characters 4-25 *) (q t0 t result) ->
       (q t0 t (array_length t))))))).
Proof.
intuition.
subst; intuition.
Save.



