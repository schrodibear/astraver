
Require Correctness.
Require Omega.
Require ZArithRing.

Require Zcomplements.
Require Zpower.

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

(*Why*) Parameter x : Z.

Lemma power1_po_1 : 
  (n: Z)
  (Pre6: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (well_founded ? (Zwf ZERO)).
Proof.
Auto with *.
Save.

Lemma power1_po_2 : 
  (n: Z)
  (Pre6: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (y1: Z)
  (n0: Z)
  (m1: Z)
  (Pre5: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Pre4: Variant1 = n0)
  (result1: bool)
  (Bool1: (if result1 then `n0 > 0` else `n0 <= 0`))
  (Test4: (if true then `n0 > 0` else `n0 <= 0`))
  (Pre3: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (result2: bool)
  (Bool2: (if result2 then (Zodd n0) else (Zeven n0)))
  (Test3: (if true then (Zodd n0) else (Zeven n0)))
  (y2: Z)
  (Post3: y2 = `y1 * m1`)
  ((m:Z)
   (m = `m1 * m1` ->
    ((n1:Z)
     (n1 = (div2 n0) -> (Zpower x n) = `y2 * (Zpower m n1)` /\ `n1 >= 0` /\
      (Zwf `0` n1 n0))))).
Proof.
Simpl; Intros.
Clear result1 Bool1 result2 Bool2.
Repeat Split; Try Omega.
Rewrite H0; Clear H0.
Decompose [and] Pre3; Clear Pre3.
Rewrite (Zodd_div2 n0 H1 Test3) in H0. Rewrite H0.
Rewrite H; Clear H.
Rewrite Post3; Clear Post3.
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
Rewrite H0; Apply Zdiv2_ge_0; Omega.
Apply Zge_le.
Rewrite H0; Apply Zdiv2_ge_0; Omega.
Rewrite H0; Apply Zdiv2_lt; Omega.
Save.

Lemma power1_po_3 : 
  (n: Z)
  (Pre6: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (y1: Z)
  (n0: Z)
  (m1: Z)
  (Pre5: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Pre4: Variant1 = n0)
  (result1: bool)
  (Bool1: (if result1 then `n0 > 0` else `n0 <= 0`))
  (Test4: (if true then `n0 > 0` else `n0 <= 0`))
  (Pre3: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (result2: bool)
  (Bool2: (if result2 then (Zodd n0) else (Zeven n0)))
  (Test2: (if false then (Zodd n0) else (Zeven n0)))
  ((m:Z)
   (m = `m1 * m1` ->
    ((n1:Z)
     (n1 = (div2 n0) -> (Zpower x n) = `y1 * (Zpower m n1)` /\ `n1 >= 0` /\
      (Zwf `0` n1 n0))))).
Proof.
Simpl; Intros.
Clear result1 Bool1 result2 Bool2.
Repeat Split; Try Omega.
Decompose [and] Pre3; Clear Pre3.
Rewrite (Zeven_div2 n0 Test2) in H1. Rewrite H1.
Rewrite H; Clear H.
Rewrite H0; Clear H0.
Rewrite Zpower_2n.
Unfold square.
Unfold div2.
Ring.
Generalize (Zdiv2_ge_0 n0); Omega.
Rewrite H0; Apply Zdiv2_ge_0; Omega.
Apply Zge_le.
Rewrite H0; Apply Zdiv2_ge_0; Omega.
Rewrite H0; Apply Zdiv2_lt; Omega.
Save.

Lemma power1_po_4 : 
  (n: Z)
  (Pre6: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (y1: Z)
  (n0: Z)
  (m1: Z)
  (Pre5: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Pre4: Variant1 = n0)
  (result1: bool)
  (Bool1: (if result1 then `n0 > 0` else `n0 <= 0`))
  (Test4: (if true then `n0 > 0` else `n0 <= 0`))
  (Pre3: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (y2: Z)
  (Post12: ((m:Z)
            (m = `m1 * m1` ->
             ((n1:Z)
              (n1 = (div2 n0) -> (Zpower x n) = `y2 * (Zpower m n1)` /\
               `n1 >= 0` /\ (Zwf `0` n1 n0))))))
  (m2: Z)
  (Post4: m2 = `m1 * m1`)
  (n1: Z)
  (Post5: n1 = (div2 n0))
  (Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0` /\ (Zwf `0` n1 n0).
Proof.
Intuition.
Save.

Lemma power1_po_5 : 
  (n: Z)
  (Pre6: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (y1: Z)
  (n0: Z)
  (m1: Z)
  (Pre5: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Pre4: Variant1 = n0)
  (result1: bool)
  (Bool1: (if result1 then `n0 > 0` else `n0 <= 0`))
  (Test4: (if true then `n0 > 0` else `n0 <= 0`))
  (Pre3: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (m2: Z)
  (n1: Z)
  (y2: Z)
  (Post11: (Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0` /\
           (Zwf `0` n1 n0))
  (Zwf `0` n1 Variant1).
Proof.
Intros; Rewrite Pre4; Tauto.
Save.

Lemma power1_po_6 : 
  (n: Z)
  (Pre6: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (y1: Z)
  (n0: Z)
  (m1: Z)
  (Pre5: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Pre4: Variant1 = n0)
  (result1: bool)
  (Bool1: (if result1 then `n0 > 0` else `n0 <= 0`))
  (Test4: (if true then `n0 > 0` else `n0 <= 0`))
  (Pre3: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (m2: Z)
  (n1: Z)
  (y2: Z)
  (Post11: (Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0` /\
           (Zwf `0` n1 n0))
  (Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0`.
Proof.
Intuition.
Save.

Lemma power1_po_7 : 
  (n: Z)
  (Pre6: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (y1: Z)
  (n0: Z)
  (m1: Z)
  (Pre5: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Pre4: Variant1 = n0)
  (result1: bool)
  (Bool1: (if result1 then `n0 > 0` else `n0 <= 0`))
  (Test1: (if false then `n0 > 0` else `n0 <= 0`))
  (Pre2: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0` /\
  ((if false then `n0 > 0` else `n0 <= 0`)).
Proof.
Intuition.
Save.

Lemma power1_po_8 : 
  (n: Z)
  (Pre6: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Zpower x n) = `y0 * (Zpower m0 n)` /\ `n >= 0`.
Proof.
Intros.
Split; [ Idtac | Omega].
Rewrite Post2; Ring.
Rewrite Post1; Trivial.
Save.

Lemma power1_po_9 : 
  (n: Z)
  (Pre6: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (m1: Z)
  (n0: Z)
  (y1: Z)
  (Post7: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0` /\
          ((if false then `n0 > 0` else `n0 <= 0`)))
  y1 = (Zpower x n).
Proof.
Intros.
Intuition.
Rewrite H.
Replace n0 with `0`.
Simpl; Ring.
Omega.
Save.

