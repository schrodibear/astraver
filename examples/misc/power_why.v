
Require Sumbool.
Require Why.
Require Omega.
Require ZArithRing.

Require Zcomplements.
Require Zpower.

Definition square := [x]`x * x`.
Definition double := [x]`2 * x`.

Definition div2 := Zdiv2.

Definition is_odd := [x](bool_of_sumbool (sumbool_not ? ? (Zeven_odd_dec x))).

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
  (Pre4: `n >= 0`)
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
  (Pre4: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (m1: Z)
  (n0: Z)
  (y1: Z)
  (Pre3: Variant1 = n0)
  (Pre2: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Test4: `n0 > 0`)
  (Test3: (Zodd n0))
  (y2: Z)
  (Post3: y2 = `y1 * m1`)
  ((m:Z)
   (m = `m1 * m1` ->
    ((n1:Z)
     (n1 = (div2 n0) -> (Zpower x n) = `y2 * (Zpower m n1)` /\ `n1 >= 0` /\
      (Zwf `0` n1 n0))))).
Proof.
Simpl; Intros.
Repeat Split; Try Omega.
Rewrite H0; Clear H0.
Decompose [and] Pre2; Clear Pre2.
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
  (Pre4: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (m1: Z)
  (n0: Z)
  (y1: Z)
  (Pre3: Variant1 = n0)
  (Pre2: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Test4: `n0 > 0`)
  (Test2: (Zeven n0))
  ((m:Z)
   (m = `m1 * m1` ->
    ((n1:Z)
     (n1 = (div2 n0) -> (Zpower x n) = `y1 * (Zpower m n1)` /\ `n1 >= 0` /\
      (Zwf `0` n1 n0))))).
Proof.
Simpl; Intros.
Repeat Split; Try Omega.
Decompose [and] Pre2; Clear Pre2.
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
  (Pre4: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (m1: Z)
  (n0: Z)
  (y1: Z)
  (Pre3: Variant1 = n0)
  (Pre2: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Test4: `n0 > 0`)
  (y2: Z)
  (Post10: ((m:Z)
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
  (Pre4: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (m1: Z)
  (n0: Z)
  (y1: Z)
  (Pre3: Variant1 = n0)
  (Pre2: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Test4: `n0 > 0`)
  (m2: Z)
  (n1: Z)
  (y2: Z)
  (Post7: (Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0` /\
          (Zwf `0` n1 n0))
  (Zwf `0` n1 Variant1).
Proof.
Intros; Rewrite Pre3; Tauto.
Save.

Lemma power1_po_6 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (m1: Z)
  (n0: Z)
  (y1: Z)
  (Pre3: Variant1 = n0)
  (Pre2: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Test4: `n0 > 0`)
  (m2: Z)
  (n1: Z)
  (y2: Z)
  (Post7: (Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0` /\
          (Zwf `0` n1 n0))
  (Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0`.
Proof.
Intuition.
Save.

Lemma power1_po_7 : 
  (n: Z)
  (Pre4: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (m1: Z)
  (n0: Z)
  (y1: Z)
  (Pre3: Variant1 = n0)
  (Pre2: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
  (Test1: `n0 <= 0`)
  (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0` /\ `n0 <= 0`.
Proof.
Intuition.
Save.

Lemma power1_po_8 : 
  (n: Z)
  (Pre4: `n >= 0`)
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
  (Pre4: `n >= 0`)
  (m0: Z)
  (Post1: m0 = x)
  (y0: Z)
  (Post2: y0 = `1`)
  (m1: Z)
  (n0: Z)
  (y1: Z)
  (Post6: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0` /\ `n0 <= 0`)
  y1 = (Zpower x n).
Proof.
Intros.
Intuition.
Rewrite H.
Replace n0 with `0`.
Simpl; Ring.
Omega.
Save.





Definition power1 := (* validation *)
  [m: Z; n: Z; y: Z; Pre4: `n >= 0`]
    let (m0, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = x x
        (refl_equal ? x)) in
      (exist_2 [m1: Z][result0: unit]m1 = x result tt Post1) in
    let (y0, result0, Post2) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = `1` `1`
        (refl_equal ? `1`)) in
      (exist_2 [y1: Z][result1: unit]y1 = `1` result0 tt Post2) in
    let (m1, n0, y1, result1, Post6) =
      (well_founded_induction Z (Zwf ZERO)
        (power1_po_1 n Pre4 m0 Post1 y0 Post2) [Variant1: Z](m1: Z)(n0: Z)
        (y1: Z)(_: Variant1 = n0)(_: (Zpower x n) = `y1 * (Zpower m1 n0)` /\
        `n0 >= 0`)
        (sig_4 Z Z Z unit [m2:Z][n1:Z][y2:Z][result:unit]
         ((Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0` /\ `n1 <= 0`))
        [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
         (m1: Z)(n0: Z)(y1: Z)(_: Variant2 = n0)
         (_: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`)
         (sig_4 Z Z Z unit [m2:Z][n1:Z][y2:Z][result:unit]
          ((Zpower x n) = `y2 * (Zpower m2 n1)` /\ `n1 >= 0` /\ `n1 <= 0`));
         m1: Z; n0: Z; y1: Z; Pre3: Variant1 = n0;
         Pre2: (Zpower x n) = `y1 * (Zpower m1 n0)` /\ `n0 >= 0`]
          let (result1, Bool1) =
            let (result3, Post9) = (Z_gt_le_bool n0 `0`) in
            (exist_1 [result4: bool]
            (if result4 then `n0 > 0` else `n0 <= 0`) result3 Post9) in
          (Cases (btest
                  [result1:bool](if result1 then `n0 > 0` else `n0 <= 0`)
                  result1 Bool1) of
          | (left Test4) =>
              let (m2, n1, y2, result2, Post6) =
                let (m2, n1, y2, result2, Post7) =
                  let (y2, result2, Post10) =
                    let (result2, Bool2) =
                      let (result4, Post11) = (is_odd n0) in
                      (exist_1 [result5: bool]
                      (if result5 then (Zodd n0) else (Zeven n0)) result4
                      Post11) in
                    (Cases (btest
                            [result2:bool](if result2 then (Zodd n0)
                                           else (Zeven n0))
                            result2 Bool2) of
                    | (left Test3) =>
                        let (y2, result3, Post3) =
                          let (result3, Post3) = (exist_1 [result3: Z]
                            result3 = `y1 * m1` `y1 * m1`
                            (refl_equal ? `y1 * m1`)) in
                          (exist_2 [y3: Z][result4: unit]
                          y3 = `y1 * m1` result3 tt Post3) in
                        (exist_2 [y3: Z][result4: unit]
                        ((m:Z)
                         (m = `m1 * m1` ->
                          ((n1:Z)
                           (n1 = (div2 n0) ->
                            (Zpower x n) = `y3 * (Zpower m n1)` /\
                            `n1 >= 0` /\ (Zwf `0` n1 n0))))) y2
                        result3
                        (power1_po_2 n Pre4 m0 Post1 y0 Post2 Variant1 m1 n0
                        y1 Pre3 Pre2 Test4 Test3 y2 Post3))
                    | (right Test2) =>
                        let (result3, Post12) = (exist_1 [result3: unit]
                          ((m:Z)
                           (m = `m1 * m1` ->
                            ((n1:Z)
                             (n1 = (div2 n0) ->
                              (Zpower x n) = `y1 * (Zpower m n1)` /\
                              `n1 >= 0` /\ (Zwf `0` n1 n0))))) tt
                          (power1_po_3 n Pre4 m0 Post1 y0 Post2 Variant1 m1
                          n0 y1 Pre3 Pre2 Test4 Test2)) in
                        (exist_2 [y2: Z][result4: unit]
                        ((m:Z)
                         (m = `m1 * m1` ->
                          ((n1:Z)
                           (n1 = (div2 n0) ->
                            (Zpower x n) = `y2 * (Zpower m n1)` /\
                            `n1 >= 0` /\ (Zwf `0` n1 n0))))) y1
                        result3 Post12) end) in
                  let (m2, result3, Post4) =
                    let (result3, Post4) = (exist_1 [result3: Z]
                      result3 = `m1 * m1` `m1 * m1`
                      (refl_equal ? `m1 * m1`)) in
                    (exist_2 [m3: Z][result4: unit]m3 = `m1 * m1` result3 
                    tt Post4) in
                  let (n1, result4, Post5) =
                    let (result4, Post5) = (exist_1 [result4: Z]
                      result4 = (div2 n0) (div2 n0)
                      (refl_equal ? (div2 n0))) in
                    (exist_2 [n2: Z][result5: unit]n2 = (div2 n0) result4 
                    tt Post5) in
                  (exist_4 [m3: Z][n2: Z][y3: Z][result5: unit]
                  (Zpower x n) = `y3 * (Zpower m3 n2)` /\ `n2 >= 0` /\
                  (Zwf `0` n2 n0) m2 n1 y2 result4
                  (power1_po_4 n Pre4 m0 Post1 y0 Post2 Variant1 m1 n0 y1
                  Pre3 Pre2 Test4 y2 Post10 m2 Post4 n1 Post5)) in
                ((wf1 n1)
                  (power1_po_5 n Pre4 m0 Post1 y0 Post2 Variant1 m1 n0 y1
                  Pre3 Pre2 Test4 m2 n1 y2 Post7) m2 n1 y2 (refl_equal ? n1)
                  (power1_po_6 n Pre4 m0 Post1 y0 Post2 Variant1 m1 n0 y1
                  Pre3 Pre2 Test4 m2 n1 y2 Post7)) in
              (exist_4 [m3: Z][n2: Z][y3: Z][result3: unit]
              (Zpower x n) = `y3 * (Zpower m3 n2)` /\ `n2 >= 0` /\
              `n2 <= 0` m2 n1 y2 result2 Post6)
          | (right Test1) =>
              let (m2, n1, y2, result2, Post6) = (exist_4 [m2: Z][n1: Z]
                [y2: Z][result2: unit](Zpower x n) = `y2 * (Zpower m2 n1)` /\
                `n1 >= 0` /\ `n1 <= 0` m1 n0 y1 tt
                (power1_po_7 n Pre4 m0 Post1 y0 Post2 Variant1 m1 n0 y1 Pre3
                Pre2 Test1)) in
              (exist_4 [m3: Z][n2: Z][y3: Z][result3: unit]
              (Zpower x n) = `y3 * (Zpower m3 n2)` /\ `n2 >= 0` /\
              `n2 <= 0` m2 n1 y2 result2 Post6) end) n m0 n y0
        (refl_equal ? n) (power1_po_8 n Pre4 m0 Post1 y0 Post2)) in
    (exist_4 [m2: Z][n1: Z][y2: Z][result2: unit]y2 = (Zpower x n) m1 
    n0 y1 result1 (power1_po_9 n Pre4 m0 Post1 y0 Post2 m1 n0 y1 Post6)).

