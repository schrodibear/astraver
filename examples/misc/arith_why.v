(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Omega.
Require Zdiv.
Require ZArithRing.

(* Why obligation from file "arith.mlw", characters 358-364 *)
Lemma mult_po_1 : 
  (x: Z)
  (y: Z)
  (Pre9: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post6: result = x)
  (result0: Z)
  (Post5: result0 = y)
  (result1: Z)
  (Post4: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre8: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
  (Test4: `a0 <> 0`)
  ~(`2` = `0`).
Proof.
Intros; Omega.
Save.

(* Why obligation from file "arith.mlw", characters 374-386 *)
Lemma mult_po_2 : 
  (x: Z)
  (y: Z)
  (Pre9: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post6: result = x)
  (result0: Z)
  (Post5: result0 = y)
  (result1: Z)
  (Post4: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre8: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
  (Test4: `a0 <> 0`)
  (Pre6: ~(`2` = `0`))
  (Test3: `(Zmod a0 2) = 1`)
  (p1: Z)
  (Post1: p1 = `p0 + b0`)
  ((a:Z)
   (a = (Zdiv a0 `2`) ->
    ((b:Z)
     (b = `2 * b0` -> (`a >= 0` /\ `p1 + a * b = x * y`) /\ (Zwf `0` a a0))))) /\
  ~(`2` = `0`).
Proof.
Intuition.
Subst a; Apply Z_div_ge0; Omega.
Rewrite (Z_div_mod_eq a0 `2`) in H2.
Rewrite <- H2.
Subst p1.
Subst a b.
Rewrite Test3.
Ring.
Omega.
Unfold Zwf. 
Repeat Split; Try Omega.
Subst a; Apply Z_div_lt; Try Omega.
Save.

(* Why obligation from file "arith.mlw", characters 355-386 *)
Lemma mult_po_3 : 
  (x: Z)
  (y: Z)
  (Pre9: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post6: result = x)
  (result0: Z)
  (Post5: result0 = y)
  (result1: Z)
  (Post4: result1 = `0`)
  (Variant1: Z)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Pre8: Variant1 = a0)
  (Inv: `a0 >= 0` /\ `p0 + a0 * b0 = x * y`)
  (Test4: `a0 <> 0`)
  (Pre6: ~(`2` = `0`))
  (Test2: `(Zmod a0 2) <> 1`)
  ((a:Z)
   (a = (Zdiv a0 `2`) ->
    ((b:Z)
     (b = `2 * b0` -> (`a >= 0` /\ `p0 + a * b = x * y`) /\ (Zwf `0` a a0))))) /\
  ~(`2` = `0`).
Proof.
Intuition.
Subst a; Apply Z_div_ge0; Try Omega.
Rewrite (Z_div_mod_eq a0 `2`) in H2.
Rewrite <- H2.
Subst a b.
Replace `a0%2` with `0`.
Ring.
Cut `2 > 0`; [ Intro h | Omega ].
Generalize (Z_mod_lt a0 `2` h).
Cut ~`a0%2 = 1`; Intros; Try Omega.
Omega.
Unfold Zwf.
Repeat Split; Try Omega.
Subst a; Apply Z_div_lt; Try Omega.
Save.

(* Why obligation from file "arith.mlw", characters 304-333 *)
Lemma mult_po_4 : 
  (x: Z)
  (y: Z)
  (Pre9: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post6: result = x)
  (result0: Z)
  (Post5: result0 = y)
  (result1: Z)
  (Post4: result1 = `0`)
  `result >= 0` /\ `result1 + result * result0 = x * y`.
Proof.
Intuition.
Subst result result0 result1; Ring.
Save.

(* Why obligation from file "arith.mlw", characters 443-445 *)
Lemma mult_po_5 : 
  (x: Z)
  (y: Z)
  (Pre9: `x >= 0` /\ `y >= 0`)
  (result: Z)
  (Post6: result = x)
  (result0: Z)
  (Post5: result0 = y)
  (result1: Z)
  (Post4: result1 = `0`)
  (a0: Z)
  (b0: Z)
  (p0: Z)
  (Inv: (`a0 >= 0` /\ `p0 + a0 * b0 = x * y`) /\ `a0 = 0`)
  `p0 = x * y`.
Proof.
Intuition.
Subst a0.
Rewrite <- H4.
Ring.
Save.


