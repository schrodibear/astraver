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

Lemma swap3_po_1 : 
  (y0: Z) 
  (x0: Z) 
  ((x:Z) (x = y0 -> ((y:Z) (y = x0 -> x = y0 /\ y = x0)))).
Proof.
Intuition.
Save.

Lemma swap3_po_2 : 
  (y0: Z) 
  (x0: Z) 
  (result: Z) 
  ((x:Z) (x = y0 -> ((y:Z) (y = result -> x = y0 /\ y = x0)))) ->
  (x1: Z) 
  x1 = y0 ->
  (y1: Z) 
  y1 = result ->
  x1 = y0 /\ y1 = x0.
Proof.
Intuition.
Save.

Lemma swap4_po_1 : 
  (y0: Z) 
  (x0: Z) 
  (tmp0: Z) 
  tmp0 = x0 ->
  (x1: Z) 
  x1 = y0 ->
  (y1: Z) 
  y1 = tmp0 ->
  x1 = y0 /\ y1 = x0.
Proof.
Intuition.
Save.

