(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Omega.
Require Zdiv.
Require ZArithRing.

Lemma mult_po_1 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma mult_po_2 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0` = `x * y`)
  (Test4: ~(a0 = `0`))
  ~(`2` = `0`).
Proof.
Intros; Omega.
Save.

Lemma mult_po_3 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0` = `x * y`)
  (Test4: ~(a0 = `0`))
  (Test3: `(Zmod a0 2)` = `1`)
  (p1: Z)
  (Post4: p1 = `p0 + b0`)
  ((a:Z)
   (a = `(Zdiv a0 2)` ->
    ((b:Z)
     (b = `2 * b0` -> `a >= 0` /\ `p1 + a * b` = `x * y` /\ (Zwf `0` a a0))))).
Proof.
Intuition.
Rewrite H3; Apply Z_div_ge0; Omega.
Rewrite (Z_div_mod_eq a0 `2`) in H2.
Rewrite <- H2.
Rewrite Post4.
Rewrite H3. Rewrite H4.
Rewrite Test3.
Ring.
Omega.
Unfold Zwf. 
Repeat Split; Try Omega.
Rewrite H3; Apply Zge_le; Apply Z_div_ge0; Omega.
Rewrite H3; Apply Z_div_lt; Try Omega.
Cut ~`a0 = 0`; [ Intro; Omega | Assumption ].
Save.

Lemma mult_po_4 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0` = `x * y`)
  (Test4: ~(a0 = `0`))
  (Test2: ~(`(Zmod a0 2)` = `1`))
  ((a:Z)
   (a = `(Zdiv a0 2)` ->
    ((b:Z)
     (b = `2 * b0` -> `a >= 0` /\ `p0 + a * b` = `x * y` /\ (Zwf `0` a a0))))).
Proof.
Intuition.
Rewrite H3; Apply Z_div_ge0; Try Omega.
Rewrite (Z_div_mod_eq a0 `2`) in H2.
Rewrite <- H2.
Rewrite H3. Rewrite H4.
Replace `a0%2` with `0`.
Ring.
Cut `2 > 0`; [ Intro h | Omega ].
Generalize (Z_mod_lt a0 `2` h).
Cut ~`a0%2 = 1`; Intros; Try Omega.
Assumption.
Omega.
Unfold Zwf.
Repeat Split; Try Omega.
Rewrite H3; Apply Zge_le; Apply Z_div_ge0; Omega.
Rewrite H3; Apply Z_div_lt; Try Omega.
Cut ~`a0 = 0`; [ Intro; Omega | Assumption ].
Save.

Lemma mult_po_5 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0` = `x * y`)
  (Test4: ~(a0 = `0`))
  (p1: Z)
  (Post12: ((a:Z)
            (a = `(Zdiv a0 2)` ->
             ((b:Z)
              (b = `2 * b0` -> `a >= 0` /\ `p1 + a * b` = `x * y` /\
               (Zwf `0` a a0))))))
  ~(`2` = `0`).
Proof.
Intros; Omega.
Save.

Lemma mult_po_6 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0` = `x * y`)
  (Test4: ~(a0 = `0`))
  (p1: Z)
  (Post12: ((a:Z)
            (a = `(Zdiv a0 2)` ->
             ((b:Z)
              (b = `2 * b0` -> `a >= 0` /\ `p1 + a * b` = `x * y` /\
               (Zwf `0` a a0))))))
  (Pre3: ~(`2` = `0`))
  (a1: Z)
  (Post5: a1 = `(Zdiv a0 2)`)
  (b1: Z)
  (Post6: b1 = `2 * b0`)
  `a1 >= 0` /\ `p1 + a1 * b1` = `x * y` /\ (Zwf `0` a1 a0).
Proof.
Intuition.
Save.

Lemma mult_po_7 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0` = `x * y`)
  (Test4: ~(a0 = `0`))
  (a1: Z)
  (b1: Z)
  (p1: Z)
  (Inv: `a1 >= 0` /\ `p1 + a1 * b1` = `x * y` /\ (Zwf `0` a1 a0))
  (Zwf `0` a1 Variant1).
Proof.
Intros; Rewrite Pre4; Tauto.
Save.

Lemma mult_po_8 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0` = `x * y`)
  (Test4: ~(a0 = `0`))
  (a1: Z)
  (b1: Z)
  (p1: Z)
  (Inv: `a1 >= 0` /\ `p1 + a1 * b1` = `x * y` /\ (Zwf `0` a1 a0))
  `a1 >= 0` /\ `p1 + a1 * b1` = `x * y`.
Proof.
Intuition.
Save.

Lemma mult_po_9 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre4: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0` = `x * y`)
  (Test1: a0 = `0`)
  `a0 >= 0` /\ `p0 + a0 * b0` = `x * y` /\ a0 = `0`.
Proof.
Intuition.
Save.

Lemma mult_po_10 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  `result >= 0` /\ `result1 + result * result0` = `x * y`.
Proof.
Intuition.
Rewrite Post1; Rewrite Post2; Rewrite Post3; Ring.
Save.

Lemma mult_po_11 : 
  (x: Z)
  (y: Z)
  (Pre5: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post1: result = x)
  (result0: Z)
  (Post2: result0 = y)
  (result1: Z)
  (Post3: result1 = `0`)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0` = `x * y` /\ a0 = `0`)
  p0 = `x * y`.
Proof.
Intuition.
Rewrite H4 in H3.
Rewrite <- H3.
Ring.
Save.

