
Require Correctness.
Require Omega.
Require ZArithRing.

Require Zcomplements.
Require Zpower.

Parameter x : Z.

Definition square := [x]`x * x`.
Definition double := [x]`2 * x`.

Definition div2 := Zdiv2.

(* Some auxiliary lemmas about Zdiv2 are necessary *)

Lemma Zdiv2_ge_0 : (x:Z) `x >= 0` -> `(Zdiv2 x) >= 0`.
Proof.
Destruct x; Auto with zarith.
Destruct p; Auto with zarith.
Simpl. Omega.
Intros. (Absurd `(NEG p) >= 0`; Red; Auto with zarith).
Save.

Lemma Zdiv2_lt : (x:Z) `x > 0` -> `(Zdiv2 x) < x`.
Proof.
Destruct x.
Intro. Absurd `0 > 0`; [ Omega | Assumption ].
Destruct p; Auto with zarith.

Simpl.
Intro p0.
Replace (POS (xI p0)) with `2*(POS p0)+1`.
Omega.
Simpl. Auto with zarith.

Intro p0.
Simpl.
Replace (POS (xO p0)) with `2*(POS p0)`.
Omega.
Simpl. Auto with zarith.

Simpl. Omega.

Intros. 
Absurd `(NEG p) > 0`; Red; Auto with zarith.
Elim p; Auto with zarith.
Omega.
Save.

(* A property of Zpower:  x^(2*n) = (x^2)^n *)

Lemma Zpower_2n : 
  (x,n:Z)`n >= 0` -> (Zpower x (double n))=(Zpower (square x) n).
Proof.
Unfold double.
Intros x0 n Hn.
Replace `2*n` with `n+n`.
Rewrite Zpower_exp.
Pattern n.
Apply natlike_ind.

Simpl. Auto with zarith.

Intros.
Unfold Zs.
Rewrite Zpower_exp.
Rewrite Zpower_exp.
Replace (Zpower x0 `1`) with x0.
Replace (Zpower (square x0) `1`) with (square x0).
Rewrite <- H0.
Unfold square.
Ring.

Unfold Zpower; Unfold Zpower_pos; Simpl. Omega.

Unfold Zpower; Unfold Zpower_pos; Simpl. Omega.

Omega.
Omega.
Omega.
Omega.
Omega.
Assumption.
Assumption.
Omega.
Save.

(* Obligations *)

Lemma power1_po_1 : 
  (n: Z) 
  `n >= 0` ->
  (m0: Z) 
  m0 = x ->
  (y0: Z) 
  y0 = `1` ->
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma power1_po_2 : 
  (n: Z) 
  `n >= 0` ->
  (m0: Z) 
  m0 = x ->
  (y0: Z) 
  y0 = `1` ->
  (Variant1: Z) 
  (y1: Z) 
  (n0: Z) 
  (m1: Z) 
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\
  `n0 >= 0` ->
  Variant1 = n0 ->
  (result1: bool) 
  (if result1 then `n0 > 0` else `n0 <= 0`) ->
  (if true then `n0 > 0` else `n0 <= 0`) ->
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\
  `n0 >= 0` ->
  (result2: bool) 
  (if result2 then (Zodd n0) else (Zeven n0)) ->
  (if true then (Zodd n0) else (Zeven n0)) ->
  (y2: Z) 
  y2 = `y1 * m1` ->
  ((m:Z)
   (m = `m1 * m1` ->
    ((n1:Z)
     (n1 = (div2 n0) -> (Zpower x n) = `y2 * (Zpower m n1)` /\ `n1 >= 0` /\
      (Zwf `0` n1 n0))))).
Proof.
Simpl; Intros.
Clear result1 H4 result2 H7.
Repeat Split; Try Omega.
Rewrite H11; Clear H11.
Decompose [and] H6; Clear H6.
Rewrite (Zodd_div2 n0 H7 H8) in H4. Rewrite H4.
Rewrite H9; Clear H9.
Rewrite H10; Clear H10.
Rewrite Zpower_exp.
Replace (Zpower m1 `1`) with m1.
Rewrite Zpower_2n.
Unfold square.
Unfold div2.
Ring.
Generalize (Zdiv2_ge_0 n0); Omega.
Unfold Zpower; Unfold Zpower_pos; Simpl; Ring.
Generalize (Zdiv2_ge_0 n0); Omega.
Omega.
Rewrite H11; Apply Zdiv2_ge_0; Omega.
Apply Zge_le.
Rewrite H11; Apply Zdiv2_ge_0; Omega.
Rewrite H11; Apply Zdiv2_lt; Omega.
Save.

Lemma power1_po_3 : 
  (n: Z) 
  `n >= 0` ->
  (m0: Z) 
  m0 = x ->
  (y0: Z) 
  y0 = `1` ->
  (Variant1: Z) 
  (y1: Z) 
  (n0: Z) 
  (m1: Z) 
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\
  `n0 >= 0` ->
  Variant1 = n0 ->
  (result1: bool) 
  (if result1 then `n0 > 0` else `n0 <= 0`) ->
  (if true then `n0 > 0` else `n0 <= 0`) ->
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\
  `n0 >= 0` ->
  (result2: bool) 
  (if result2 then (Zodd n0) else (Zeven n0)) ->
  (if false then (Zodd n0) else (Zeven n0)) ->
  ((m:Z)
   (m = `m1 * m1` ->
    ((n1:Z)
     (n1 = (div2 n0) -> (Zpower x n) = `y1 * (Zpower m n1)` /\ `n1 >= 0` /\
      (Zwf `0` n1 n0))))).
Proof.
Simpl; Intros.
Clear result1 H4 result2 H7.
Repeat Split; Try Omega.
Decompose [and] H6; Clear H6.
Rewrite (Zeven_div2 n0 H8) in H4. Rewrite H4.
Rewrite H9; Clear H9.
Rewrite H10; Clear H10.
Rewrite Zpower_2n.
Unfold square.
Unfold div2.
Ring.
Generalize (Zdiv2_ge_0 n0); Omega.
Rewrite H10; Apply Zdiv2_ge_0; Omega.
Apply Zge_le.
Rewrite H10; Apply Zdiv2_ge_0; Omega.
Rewrite H10; Apply Zdiv2_lt; Omega.
Save.

Lemma power1_po_4 : 
  (n: Z) 
  `n >= 0` ->
  (m0: Z) 
  m0 = x ->
  (y0: Z) 
  y0 = `1` ->
  (Variant1: Z) 
  (y1: Z) 
  (n0: Z) 
  (m1: Z) 
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\
  `n0 >= 0` ->
  Variant1 = n0 ->
  (result1: bool) 
  (if result1 then `n0 > 0` else `n0 <= 0`) ->
  (if true then `n0 > 0` else `n0 <= 0`) ->
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\
  `n0 >= 0` ->
  (y2: Z) 
  ((m:Z)
   (m = `m1 * m1` ->
    ((n1:Z)
     (n1 = (div2 n0) -> (Zpower x n) = `y2 * (Zpower m n1)` /\ `n1 >= 0` /\
      (Zwf `0` n1 n0))))) ->
  (m2: Z) 
  m2 = `m1 * m1` ->
  (n1: Z) 
  n1 = (div2 n0) ->
  (Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0` /\ (Zwf `0` n1 n0).
Proof.
Intuition.
Save.

Lemma power1_po_5 : 
  (n: Z) 
  `n >= 0` ->
  (m0: Z) 
  m0 = x ->
  (y0: Z) 
  y0 = `1` ->
  (Variant1: Z) 
  (y1: Z) 
  (n0: Z) 
  (m1: Z) 
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\
  `n0 >= 0` ->
  Variant1 = n0 ->
  (result1: bool) 
  (if result1 then `n0 > 0` else `n0 <= 0`) ->
  (if true then `n0 > 0` else `n0 <= 0`) ->
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\
  `n0 >= 0` ->
  (m2: Z) 
  (n1: Z) 
  (y2: Z) 
  (Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0` /\
  (Zwf `0` n1 n0) ->
  (Zwf `0` n1 Variant1).
Proof.
Intros; Rewrite H3; Tauto.
Save.

Lemma power1_po_6 : 
  (n: Z) 
  `n >= 0` ->
  (m0: Z) 
  m0 = x ->
  (y0: Z) 
  y0 = `1` ->
  (Variant1: Z) 
  (y1: Z) 
  (n0: Z) 
  (m1: Z) 
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\
  `n0 >= 0` ->
  Variant1 = n0 ->
  (result1: bool) 
  (if result1 then `n0 > 0` else `n0 <= 0`) ->
  (if true then `n0 > 0` else `n0 <= 0`) ->
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\
  `n0 >= 0` ->
  (m2: Z) 
  (n1: Z) 
  (y2: Z) 
  (Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0` /\
  (Zwf `0` n1 n0) ->
  (Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0`.
Proof.
Intuition.
Save.

Lemma power1_po_7 : 
  (n: Z) 
  `n >= 0` ->
  (m0: Z) 
  m0 = x ->
  (y0: Z) 
  y0 = `1` ->
  (Variant1: Z) 
  (y1: Z) 
  (n0: Z) 
  (m1: Z) 
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\
  `n0 >= 0` ->
  Variant1 = n0 ->
  (result1: bool) 
  (if result1 then `n0 > 0` else `n0 <= 0`) ->
  (if false then `n0 > 0` else `n0 <= 0`) ->
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\
  `n0 >= 0` ->
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0` /\
  ((if false then `n0 > 0` else `n0 <= 0`)).
Proof.
Intuition.
Save.

Lemma power1_po_8 : 
  (n: Z) 
  `n >= 0` ->
  (m0: Z) 
  m0 = x ->
  (y0: Z) 
  y0 = `1` ->
  (Zpower x n) = `y0 * (Zpower m0 n)` /\ `n >= 0`.
Proof.
Intros.
Split; [ Idtac | Omega].
Rewrite H1; Ring.
Rewrite H0; Trivial.
Save.

Lemma power1_po_9 : 
  (n: Z) 
  `n >= 0` ->
  (m0: Z) 
  m0 = x ->
  (y0: Z) 
  y0 = `1` ->
  (m1: Z) 
  (n0: Z) 
  (y1: Z) 
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0` /\
  ((if false then `n0 > 0` else `n0 <= 0`)) ->
  y1 = (Zpower x n).
Proof.
Intros.
Intuition.
Rewrite H3.
Replace n0 with `0`.
Simpl; Ring.
Omega.
Save.

