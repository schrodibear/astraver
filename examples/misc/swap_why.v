Require Omega.

Lemma swap1_po_1 : 
  (x: Z) 
  (y: Z) 
  (result: Z) 
  result = x ->
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
  (result: Z) 
  result = x ->
  (x0: Z) 
  x0 = y ->
  (y0: Z) 
  y0 = result ->
  x0 = y /\ y0 = x.
Proof.
Intuition.
Save.

Lemma swap3_po_1 : 
  (a: Z) 
  (b: Z) 
  (result: Z) 
  result = a ->
  (a0: Z) 
  a0 = b ->
  (b0: Z) 
  b0 = result ->
  a0 = b /\ b0 = a.
Proof.
Intuition.
Save.

Lemma swap4_po_1 : 
  (a: Z) 
  (b: Z) 
  (tmp0: Z) 
  tmp0 = a ->
  (a0: Z) 
  a0 = b ->
  (b0: Z) 
  b0 = tmp0 ->
  a0 = b /\ b0 = a.
Proof.
Intuition.
Save.


Lemma call_swap3_y_x_po_1 : 
  (x: Z) 
  (y: Z) 
  (y0: Z) 
  (x0: Z) 
  y0 = x /\ x0 = y ->
  x0 = y /\ y0 = x.
Proof.
Intuition.
Save.

Lemma call_swap4_x_y_po_1 : 
  (x: Z) 
  (y: Z) 
  x = `3` ->
  (x0: Z) 
  (y0: Z) 
  x0 = y /\ y0 = x ->
  y0 = `3`.
Proof.
Intuition.
Save.

Lemma call_swap4_y_x_po_1 : 
  (x: Z) 
  (y: Z) 
  x = `3` ->
  (y0: Z) 
  (x0: Z) 
  y0 = x /\ x0 = y ->
  y0 = `3`.
Proof.
Intuition.
Save.

Lemma test_swap3_po_1 : 
  (result: Z) 
  result = `1` ->
  (result0: Z) 
  result0 = `2` ->
  (c0: Z) 
  (d0: Z) 
  c0 = result0 /\ d0 = result ->
  d0 = `1`.
Proof.
Intuition.
Save.

Lemma test_swap4_po_1 : 
  (result: Z) 
  result = `1` ->
  (result0: Z) 
  result0 = `2` ->
  (c0: Z) 
  (d0: Z) 
  c0 = result0 /\ d0 = result ->
  d0 = `1`.
Proof.
Intuition.
Save.

