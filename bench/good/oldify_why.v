
Require Import Why.

(*Why logic*) Definition q1 : Z -> Z -> Z -> Prop.
Admitted.



(*Why*) Parameter f1 :
  forall (y: Z), forall (r: Z),
  (sig_2 Z unit (fun (r0: Z) (result: unit)  => ((q1 r0 r y)))).

(*Why*) Parameter g1_valid :
  forall (_: unit), forall (r: Z),
  (sig_2 Z unit (fun (r0: Z) (result: unit)  => ((q1 r0 r r)))).

(*Why logic*) Definition q : (array Z) -> (array Z) -> Z -> Prop.
Admitted.



(*Why*) Parameter f :
  forall (x: Z), forall (t: (array Z)),
  (sig_2 (array Z) unit (fun (t0: (array Z)) (result: unit)  => ((q t0 t x)))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_po_1 : 
  forall (t: (array Z)),
  forall (result: Z),
  forall (HW_1: result = (array_length t)),
  forall (t0: (array Z)),
  forall (HW_2: (q t0 t result)),
  (q t0 t (array_length t)).
Proof.
intuition.
subst; intuition.
Save.

(*Why*) Parameter g_valid :
  forall (t: (array Z)),
  (sig_2 (array Z) unit
   (fun (t0: (array Z)) (result: unit)  => ((q t0 t (array_length t))))).

