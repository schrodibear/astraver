
Require Import Why.

Parameter q : array Z -> array Z -> Z -> Prop.

Parameter q1 : Z -> Z -> Z -> Prop.

(*Why*) Parameter f1 :
  forall (y: Z), forall (r: Z),
  (sig_2 Z unit (fun (r0: Z) (result: unit)  => ((q1 r0 r y)))).

(*Why*) Parameter f :
  forall (x: Z), forall (t: (array Z)),
  (sig_2 (array Z) unit (fun (t0: (array Z)) (result: unit)  => ((q t0 t x)))).

