Require Omega.

Lemma swap1_po_1 : 
  (y: Z) 
  (x: Z) 
  ((x0:Z) (x0 = y -> ((y0:Z) (y0 = x -> x0 = y /\ y0 = x)))).
Proof.
Intuition.
Save.

Lemma swap1_po_2 : 
  (y: Z) 
  (x: Z) 
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
  (y: Z) 
  (x: Z) 
  ((x0:Z) (x0 = y -> ((y0:Z) (y0 = x -> x0 = y /\ y0 = x)))).
Proof.
Intuition.
Save.

Lemma swap2_po_2 : 
  (y: Z) 
  (x: Z) 
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

