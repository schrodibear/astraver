Require Omega.

Lemma swap1_po_1 : 
  (x: Z) 
  (y: Z) 
  ((x0:Z) (x0 = y -> ((y0:Z) (y0 = x -> x0 = y /\ y0 = x)))).
Proof.
Intuition.
Save.

Lemma swap1_po_2 : 
  (x: Z) 
  (y: Z) 
  (result: Z) 
  ((x0:Z) (x0 = y -> ((y0:Z) (y0 = result -> x0 = y /\ y0 = x)))) ->
  (x0: Z) 
  x0 = y ->
  (y0: Z) 
  y0 = result ->
  x0 = y /\ y0 = x.
Proof.
Intuition.
Save.


Lemma swap2_po_1 : 
  (x: Z) 
  (y: Z) 
  ((x0:Z) (x0 = y -> ((y0:Z) (y0 = x -> x0 = y /\ y0 = x)))).
Proof.
Intuition.
Save.

Lemma swap2_po_2 : 
  (x: Z) 
  (y: Z) 
  (result: Z) 
  ((x0:Z) (x0 = y -> ((y0:Z) (y0 = result -> x0 = y /\ y0 = x)))) ->
  (x0: Z) 
  x0 = y ->
  (y0: Z) 
  y0 = result ->
  x0 = y /\ y0 = x.
Proof.
Intuition.
Save.

