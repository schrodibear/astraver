
Require Why.

Parameter q : (array Z) -> (array Z) -> Z -> Prop.

Parameter q1 : Z -> Z -> Z -> Prop.

(*Why*) Parameter f1 :
  (y: Z)(r: Z)(sig_2 Z unit [r0: Z][result: unit]((q1 r0 r y))).

Definition g1 := (* validation *)
  [r: Z]
    let (r0, result1, Post1) = (f1 r r) in
    (exist_2 [r1: Z][result2: unit](q1 r1 r r) r0 result1 Post1).

(*Why*) Parameter f :
  (x: Z)(t: (array Z))
  (sig_2 (array Z) unit [t0: (array Z)][result: unit]((q t0 t x))).

Definition g := (* validation *)
  [t: (array Z)]
    let (t0, result1, Post1) = (f (array_length t) t) in
    (exist_2 [t1: (array Z)][result2: unit](q t1 t (array_length t)) 
    t0 result1 Post1).

