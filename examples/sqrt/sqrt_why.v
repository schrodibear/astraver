(********************************************************************

  A simple algorithm for computing the square root of a non-negative
  integer.

  Proofs of obligations generated by Why.

  (c) Claude March�, may 2002

**********************************************************************)

(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)


Require ZArith.
Add LoadPath "/users/demons/filliatr/local/soft/why/lib/coq".
Require Zcomplements.
Require ZArithRing.
Require Zdiv.
Require Omega.
Require Why.

(* some basic arithmetic lemmas *)

Lemma sqr_gt:(x,y:Z)`x > y`->`y > 0`->`x*x > y*y`.
Proof.
Intros.
Assert `x*y > y*y`.
Apply Zgt_Zmult_right; Omega.
Assert `x*x > x*y`.
Apply Zgt_Zmult_left; Omega.
Omega.
Save.

Lemma Z_mod_same : (a:Z)`a>0`->`a%a=0`.
Proof.
Intros a aPos.
Generalize (Z_mod_plus `0` `1` a aPos).
Replace `0+1*a` with `a`.
Intros.
Rewrite H.
Compute.
Trivial.
Ring.
Save.

Lemma Z_div_same : (a:Z)`a>0`->`a/a=1`.
Proof.
Intros a aPos.
Generalize (Z_div_plus `0` `1` a aPos).
Replace `0+1*a` with `a`.
Intros.
Rewrite H.
Compute.
Trivial.
Ring.
Save.

(* some general lemmas for invariants *)

Lemma iter_sqrt_pos: (x,z:Z)`x>0`->`z>0`->`(x/z+z)/2>0`.
Proof.
Intros x z xPos zPos.
Assert `(x/z+z)>=2`.
Assert `(x+z*z)>=z+z`.
Assert `x+(z-1)*(z-1) >= 1`.
Generalize (sqr_pos `z-1`).
Intros.
Omega.
Replace `z*z` with `(z-1)*(z-1)+z+z-1`.
Omega.
Ring.
Generalize (Z_div_ge `x+z*z` `z+z` `z` zPos H).
Intro.
Generalize (Z_div_plus x z z zPos).
Intro H1.
Rewrite H1 in H0.
Clear H1.
Generalize (Z_div_plus z `1` z zPos).
Replace `1*z` with `z`.
Intro H2.
Rewrite H2 in H0.
Clear H2.
Generalize (Z_div_plus `0` `1` z zPos).
Replace `1*z` with `z`.
Replace `0+z` with `z`.
Intro.
Rewrite H1 in H0.
Simpl in H0.
Trivial.
Trivial.
Ring.
Ring.
Assert `2>0`.
Omega.
Generalize (Z_div_ge `x/z+z` `2` `2` H0 H).
Replace `2/2` with `1`.
Intro; Omega.
Compute.
Trivial.
Save.

Lemma iter_sqrt_pos2 : (x:Z)`x>0`->`(x+1)/2>0`.
Proof.
Intros.
Assert `x+1 >= 2`. Omega.
Assert `(x+1)/2 >= 2/2`.
Apply Z_div_ge; Try Omega.
Assert `2/2 > 0`; Try Omega.
Compute; Trivial.
Save.

Lemma iter_sqrt_invar1: (x,y,z:Z)
  `x>0`->`y>0`->`z=(x/y+y)/2`->`2*y*z<=x+y*y`.
Proof.
Intros x y z xPos yPos zVal.
Assert `2*z <= x/y+y`.
Rewrite zVal.
Apply Z_mult_div_ge; Omega.
Assert `2*y*z <= y*(x/y+y)`.
Replace `2*y*z` with `y*(2*z)`; Try Ring.
Apply Zle_Zmult_pos_left; Trivial Orelse Omega.
Assert `y*(x/y+y) <= x+y*y`.
Assert `y*(x/y+y) = y*(x/y)+y*y`; Try Ring. 
Assert `y*(x/y) <= x`.
Apply Z_mult_div_ge; Omega.
Omega.
Omega.
Save.

Lemma iter_sqrt_invar2: (x,y,z:Z)
  `x>0`->`y>0`->`z=(x/y+y)/2`->`2*y*(z+1)>x+y*y`.
Proof.
Intros x y z xPos yPos zVal.
Assert TwoPos:`2>0`; Try Omega.
Generalize (Z_div_mod_eq x y yPos).
Generalize (Z_mod_lt x y yPos).
Generalize (Z_div_mod_eq `x/y+y` `2` TwoPos).
Generalize (Z_mod_lt `x/y+y` `2` TwoPos).
Intros.
Rewrite zVal.
Replace `2*y*((x/y+y)/2+1)` with `y*(2*((x/y+y)/2))+y+y`; 
  Try Ring.
Replace `2*((x/y+y)/2)` with `x/y+y - (x/y+y)%2`.
Replace `y*(x/y+y-(x/y+y)%2)` with `y*(x/y)+y*y-y*((x/y+y)%2)`.
Replace `y*(x/y)` with `x - x%y`.
Assert `y >= y*((x/y+y)%2)`.
Pattern 1 y; Replace `y` with `y*1`.
Apply Zge_Zmult_pos_left.
Omega.
Omega.
Ring.
Omega.
Omega.
Ring.
Omega.
Save.

Lemma iter_sqrt_invar3: (x,y,z:Z)
`x>0` -> `y>0` -> `z=(x/y+y)/2` -> `x<(z+1)*(z+1)`.
Proof.
Intros x y z xPos yPos zVal.
Cut `(z+1)*(z+1)-x > 0 `; Try Omega.
Assert `(4*y*y)*((z+1)*(z+1)-x) >= 1`.
Replace `(4*y*y)*((z+1)*(z+1)-x)` with
  `(2*y*(z+1))*(2*y*(z+1)) - 4*y*y*x`; Try Ring.
Generalize (iter_sqrt_invar2 x y z xPos yPos zVal).
Intro.
Assert `2*y*(z+1)*(2*y*(z+1)) > (x+y*y)*(x+y*y)`.
Assert `2*y*(z+1)*(x+y*y) > (x+y*y)*(x+y*y)`.
Apply Zgt_Zmult_right.
Generalize (sqr_pos y).
Omega.
Assumption.
Assert `2*y*(z+1)*(2*y*(z+1)) > 2*y*(z+1)*(x+y*y)`; Try Omega.
Apply Zgt_Zmult_left; Try Assumption.
Apply Zgt_ZERO_mult; Try Omega.
Assert `z>=0`; Try Omega.
Rewrite zVal.
Apply Z_div_ge0; Try Omega.
Assert `x/y>=0`; Try Omega.
Apply Z_div_ge0; Try Omega.
Assert `(x+y*y)*(x+y*y)-4*y*y*x >=0`; Try Omega.
Replace `(x+y*y)*(x+y*y)-4*y*y*x` with `(x-y*y)*(x-y*y)`; Try Ring.
Apply sqr_pos.
Apply (Zmult_gt `4*y*y`).
Apply Zgt_ZERO_mult; Try Omega.
Omega.
Save.




Lemma iter_sqrt_invar4: (x,y,z:Z)
`x>0` -> `y>0` -> `z=(x/y+y)/2` -> `z>=y` -> `y*y<= x`.
Proof.
Intros x y z xPos yPos zVal zGey.
Generalize (iter_sqrt_invar1 x y z xPos yPos zVal); Intros.
Assert `y*y <= y*z`.
Apply Zle_Zmult_pos_left; Try Omega.
Assert `2*y*z = y*z+y*z`; Try Ring.
Omega.
Save.




(* beginning of proof obligations *)

Lemma sqrt_po_1 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test6: `x = 0`)
  `0 * 0 <= x` /\ `x < (0 + 1) * (0 + 1)`.
Proof. (* sqrt_po_1 *)
Auto with *.
Save.

Lemma sqrt_po_2 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test4: `x <= 3`)
  `1 * 1 <= x` /\ `x < (1 + 1) * (1 + 1)`.
Proof. (* sqrt_po_2 *)
Auto with *.
Save.

Lemma sqrt_po_3 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (result1: Z)
  (Post1: result1 = x)
  ~(`2` = `0`).
Proof. (* sqrt_po_3 *)
Auto with *.
Save.

Lemma sqrt_po_4 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (result1: Z)
  (Post1: result1 = x)
  (Pre1: ~(`2` = `0`))
  (result2: Z)
  (Post2: result2 = `(Zdiv (x + 1) 2)`)
  (well_founded ? (Zwf ZERO)).
Proof. (* sqrt_po_4 *)
Auto with *.
Save.


Lemma sqrt_po_5 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (result1: Z)
  (Post1: result1 = x)
  (Pre1: ~(`2` = `0`))
  (result2: Z)
  (Post2: result2 = `(Zdiv (x + 1) 2)`)
  (Variant1: Z)
  (y0: Z)
  (z0: Z)
  (Pre6: Variant1 = y0)
  (Pre5: `z0 > 0` /\ `y0 > 0` /\ `z0 = (Zdiv ((Zdiv x y0) + y0) 2)` /\
         `x < (y0 + 1) * (y0 + 1)` /\ `x < (z0 + 1) * (z0 + 1)`)
  (Test2: `z0 < y0`)
  (y1: Z)
  (Post3: y1 = z0)
  (Pre3: ~(`2` = `0`))
  ~(z0 = `0`).
Proof. (* sqrt_po_5 *)
Auto with *.
Save.

Lemma sqrt_po_6 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (result1: Z)
  (Post1: result1 = x)
  (Pre1: ~(`2` = `0`))
  (result2: Z)
  (Post2: result2 = `(Zdiv (x + 1) 2)`)
  (Variant1: Z)
  (y0: Z)
  (z0: Z)
  (Pre6: Variant1 = y0)
  (Pre5: `z0 > 0` /\ `y0 > 0` /\ `z0 = (Zdiv ((Zdiv x y0) + y0) 2)` /\
         `x < (y0 + 1) * (y0 + 1)` /\ `x < (z0 + 1) * (z0 + 1)`)
  (Test2: `z0 < y0`)
  (y1: Z)
  (Post3: y1 = z0)
  (Pre3: ~(`2` = `0`))
  (Pre4: ~(z0 = `0`))
  (z1: Z)
  (Post4: z1 = `(Zdiv ((Zdiv x z0) + z0) 2)`)
  `z1 > 0` /\ `y1 > 0` /\ `z1 = (Zdiv ((Zdiv x y1) + y1) 2)` /\
  `x < (y1 + 1) * (y1 + 1)` /\ `x < (z1 + 1) * (z1 + 1)` /\ (Zwf `0` y1 y0).
Proof. (* sqrt_po_6 *)
Unfold Zwf.
Intuition.
Rewrite Post4.
Apply iter_sqrt_pos; Omega.
Rewrite Post3; Assumption.
Rewrite Post3; Assumption.
Apply (iter_sqrt_invar3 x z0); Auto.
Omega.
Save.

Lemma sqrt_po_7 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (result1: Z)
  (Post1: result1 = x)
  (Pre1: ~(`2` = `0`))
  (result2: Z)
  (Post2: result2 = `(Zdiv (x + 1) 2)`)
  (Variant1: Z)
  (y0: Z)
  (z0: Z)
  (Pre6: Variant1 = y0)
  (Pre5: `z0 > 0` /\ `y0 > 0` /\ `z0 = (Zdiv ((Zdiv x y0) + y0) 2)` /\
         `x < (y0 + 1) * (y0 + 1)` /\ `x < (z0 + 1) * (z0 + 1)`)
  (Test2: `z0 < y0`)
  (y1: Z)
  (z1: Z)
  (Post6: `z1 > 0` /\ `y1 > 0` /\ `z1 = (Zdiv ((Zdiv x y1) + y1) 2)` /\
          `x < (y1 + 1) * (y1 + 1)` /\ `x < (z1 + 1) * (z1 + 1)` /\
          (Zwf `0` y1 y0))
  (Zwf `0` y1 Variant1).
Proof. (* sqrt_po_7 *)
Unfold Zwf.
Intuition; Trivial.
Save.

Lemma sqrt_po_8 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (result1: Z)
  (Post1: result1 = x)
  (Pre1: ~(`2` = `0`))
  (result2: Z)
  (Post2: result2 = `(Zdiv (x + 1) 2)`)
  (Variant1: Z)
  (y0: Z)
  (z0: Z)
  (Pre6: Variant1 = y0)
  (Pre5: `z0 > 0` /\ `y0 > 0` /\ `z0 = (Zdiv ((Zdiv x y0) + y0) 2)` /\
         `x < (y0 + 1) * (y0 + 1)` /\ `x < (z0 + 1) * (z0 + 1)`)
  (Test2: `z0 < y0`)
  (y1: Z)
  (z1: Z)
  (Post6: `z1 > 0` /\ `y1 > 0` /\ `z1 = (Zdiv ((Zdiv x y1) + y1) 2)` /\
          `x < (y1 + 1) * (y1 + 1)` /\ `x < (z1 + 1) * (z1 + 1)` /\
          (Zwf `0` y1 y0))
  `z1 > 0` /\ `y1 > 0` /\ `z1 = (Zdiv ((Zdiv x y1) + y1) 2)` /\
  `x < (y1 + 1) * (y1 + 1)` /\ `x < (z1 + 1) * (z1 + 1)`.
Proof. (* sqrt_po_8 *)
Intuition Try Omega.
Save.



Lemma sqrt_po_9 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (result1: Z)
  (Post1: result1 = x)
  (Pre1: ~(`2` = `0`))
  (result2: Z)
  (Post2: result2 = `(Zdiv (x + 1) 2)`)
  (Variant1: Z)
  (y0: Z)
  (z0: Z)
  (Pre6: Variant1 = y0)
  (Pre5: `z0 > 0` /\ `y0 > 0` /\ `z0 = (Zdiv ((Zdiv x y0) + y0) 2)` /\
         `x < (y0 + 1) * (y0 + 1)` /\ `x < (z0 + 1) * (z0 + 1)`)
  (Test1: `z0 >= y0`)
  `z0 > 0` /\ `y0 > 0` /\ `z0 = (Zdiv ((Zdiv x y0) + y0) 2)` /\
  `x < (y0 + 1) * (y0 + 1)` /\ `x < (z0 + 1) * (z0 + 1)` /\ `z0 >= y0`.
Proof. (* sqrt_po_9 *)
Intuition.
Save.

Lemma sqrt_po_10 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (result1: Z)
  (Post1: result1 = x)
  (Pre1: ~(`2` = `0`))
  (result2: Z)
  (Post2: result2 = `(Zdiv (x + 1) 2)`)
  `result2 > 0` /\ `result1 > 0` /\
  `result2 = (Zdiv ((Zdiv x result1) + result1) 2)` /\
  `x < (result1 + 1) * (result1 + 1)` /\ `x < (result2 + 1) * (result2 + 1)`.
Proof.
Intuition.
Rewrite Post2.
Assert `(x+1)/2 >= 1`.
Pattern 2 `1`; Replace `1` with `2/2`; Trivial.
Apply Z_div_ge; Try Omega.
Omega.
Rewrite Post1.
Assert `x/x+x = x+1`.
Assert xPos:`x>0`; Try Omega.
Generalize (Z_div_same x xPos). 
Intro.
Rewrite H; Omega.
Rewrite H; Trivial.

Rewrite Post1.
Assert `(x+1)*(x+1) >= (x+1)*1`.
Apply Zge_Zmult_pos_left; Try Omega.
Assert `(x+1)*1 = x+1`; Try Ring.
Omega.

Rewrite Post2.
Apply (iter_sqrt_invar3 x x); Try Omega.
Assert `x/x+x = x+1`.
Assert xPos:`x>0`; Try Omega.
Generalize (Z_div_same x xPos). 
Intro.
Rewrite H; Omega.
Rewrite H; Trivial.
Save.


Lemma sqrt_po_11 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (result1: Z)
  (Post1: result1 = x)
  (Pre1: ~(`2` = `0`))
  (result2: Z)
  (Post2: result2 = `(Zdiv (x + 1) 2)`)
  (y0: Z)
  (z0: Z)
  (Post5: `z0 > 0` /\ `y0 > 0` /\ `z0 = (Zdiv ((Zdiv x y0) + y0) 2)` /\
          `x < (y0 + 1) * (y0 + 1)` /\ `x < (z0 + 1) * (z0 + 1)` /\
          `z0 >= y0`)
  `y0 * y0 <= x` /\ `x < (y0 + 1) * (y0 + 1)`.
Proof.
Intuition.
Apply (iter_sqrt_invar4 x y0 z0); Try Omega.
Save.

Definition sqrt := (* validation *)
  [x: Z; Pre7: `x >= 0`]
    let (result, Post9) =
      let (result, Bool3) =
        let (result1, Post10) = (Z_eq_bool x `0`) in
        (exist_1 [result2: bool]
        (if result2 then `x = 0` else `x <> 0`) result1 Post10) in
      (Cases (btest [result:bool](if result then `x = 0` else `x <> 0`)
              result Bool3) of
      | (left Test6) =>
          let (result0, Post19) = (exist_1 [result0: Z]
            `result0 * result0 <= x` /\
            `x < (result0 + 1) * (result0 + 1)` `0`
            (sqrt_po_1 x Pre7 Test6)) in
          (exist_1 [result1: Z]`result1 * result1 <= x` /\
          `x < (result1 + 1) * (result1 + 1)` result0 Post19)
      | (right Test5) =>
          let (result0, Post11) =
            let (result0, Bool2) =
              let (result2, Post12) = (Z_le_gt_bool x `3`) in
              (exist_1 [result3: bool]
              (if result3 then `x <= 3` else `x > 3`) result2 Post12) in
            (Cases (btest
                    [result0:bool](if result0 then `x <= 3` else `x > 3`)
                    result0 Bool2) of
            | (left Test4) =>
                let (result1, Post18) = (exist_1 [result1: Z]
                  `result1 * result1 <= x` /\
                  `x < (result1 + 1) * (result1 + 1)` `1`
                  (sqrt_po_2 x Pre7 Test5 Test4)) in
                (exist_1 [result2: Z]`result2 * result2 <= x` /\
                `x < (result2 + 1) * (result2 + 1)` result1 Post18)
            | (right Test3) =>
                let (result1, Post13) =
                  let (result1, Post1) = (exist_1 [result1: Z]result1 = x 
                    x (refl_equal ? x)) in
                  let (y0, result2, Post14) =
                    let Pre1 =
                      (sqrt_po_3 x Pre7 Test5 Test3 result1 Post1) in
                    let (result2, Post2) = (exist_1 [result2: Z]
                      result2 = `(Zdiv (x + 1) 2)` `(Zdiv (x + 1) 2)`
                      (refl_equal ? `(Zdiv (x + 1) 2)`)) in
                    let (y0, z0, result3, Post15) =
                      let (y0, z0, result3, Post5) =
                        (well_founded_induction Z (Zwf ZERO)
                          (sqrt_po_4 x Pre7 Test5 Test3 result1 Post1 Pre1
                          result2 Post2) [Variant1: Z](y0: Z)(z0: Z)
                          (_: Variant1 = y0)(_0: `z0 > 0` /\ `y0 > 0` /\
                          `z0 = (Zdiv ((Zdiv x y0) + y0) 2)` /\
                          `x < (y0 + 1) * (y0 + 1)` /\
                          `x < (z0 + 1) * (z0 + 1)`)
                          (sig_3 Z Z unit [y1: Z][z1: Z][result3: unit]
                           (`z1 > 0` /\ `y1 > 0` /\
                           `z1 = (Zdiv ((Zdiv x y1) + y1) 2)` /\
                           `x < (y1 + 1) * (y1 + 1)` /\
                           `x < (z1 + 1) * (z1 + 1)` /\ `z1 >= y1`))
                          [Variant1: Z; wf1: (Variant2: Z)
                           (Pre2: (Zwf `0` Variant2 Variant1))(y0: Z)(z0: Z)
                           (_: Variant2 = y0)(_0: `z0 > 0` /\ `y0 > 0` /\
                           `z0 = (Zdiv ((Zdiv x y0) + y0) 2)` /\
                           `x < (y0 + 1) * (y0 + 1)` /\
                           `x < (z0 + 1) * (z0 + 1)`)
                           (sig_3 Z Z unit [y1: Z][z1: Z][result3: unit]
                            (`z1 > 0` /\ `y1 > 0` /\
                            `z1 = (Zdiv ((Zdiv x y1) + y1) 2)` /\
                            `x < (y1 + 1) * (y1 + 1)` /\
                            `x < (z1 + 1) * (z1 + 1)` /\ `z1 >= y1`));
                           y0: Z; z0: Z; Pre6: Variant1 = y0;
                           Pre5: `z0 > 0` /\ `y0 > 0` /\
                           `z0 = (Zdiv ((Zdiv x y0) + y0) 2)` /\
                           `x < (y0 + 1) * (y0 + 1)` /\
                           `x < (z0 + 1) * (z0 + 1)`]
                            let (result3, Bool1) =
                              let (result5, Post16) = (Z_lt_ge_bool z0 y0) in
                              (exist_1 [result6: bool]
                              (if result6 then `z0 < y0` else `z0 >= y0`) 
                              result5 Post16) in
                            (Cases (btest
                                    [result3:bool](if result3 then `z0 < y0`
                                                   else `z0 >= y0`)
                                    result3 Bool1) of
                            | (left Test2) =>
                                let (y1, z1, result4, Post5) =
                                  let (y1, z1, result4, Post6) =
                                    let (y1, result4, Post3) =
                                      let (result4, Post3) =
                                        (exist_1 [result4: Z]result4 = z0 
                                        z0 (refl_equal ? z0)) in
                                      (exist_2 [y2: Z][result5: unit]
                                      y2 = z0 result4 tt Post3) in
                                    let Pre3 = Pre1 in
                                    let Pre4 =
                                      (sqrt_po_5 x Pre7 Test5 Test3 result1
                                      Post1 Pre1 result2 Post2 Variant1 y0 z0
                                      Pre6 Pre5 Test2 y1 Post3 Pre3) in
                                    let (z1, result5, Post4) =
                                      let (result5, Post4) =
                                        (exist_1 [result5: Z]
                                        result5 =
                                        `(Zdiv ((Zdiv x z0) + z0) 2)` 
                                        `(Zdiv ((Zdiv x z0) + z0) 2)`
                                        (refl_equal ? `(Zdiv ((Zdiv x z0) +
                                                             z0)
                                                        2)`)) in
                                      (exist_2 [z2: Z][result6: unit]
                                      z2 = `(Zdiv ((Zdiv x z0) + z0) 2)` 
                                      result5 tt Post4) in
                                    (exist_3 [y2: Z][z2: Z][result6: unit]
                                    `z2 > 0` /\ `y2 > 0` /\
                                    `z2 = (Zdiv ((Zdiv x y2) + y2) 2)` /\
                                    `x < (y2 + 1) * (y2 + 1)` /\
                                    `x < (z2 + 1) * (z2 + 1)` /\
                                    (Zwf `0` y2 y0) y1 z1 result5
                                    (sqrt_po_6 x Pre7 Test5 Test3 result1
                                    Post1 Pre1 result2 Post2 Variant1 y0 z0
                                    Pre6 Pre5 Test2 y1 Post3 Pre3 Pre4 z1
                                    Post4)) in
                                  ((wf1 y1)
                                    (sqrt_po_7 x Pre7 Test5 Test3 result1
                                    Post1 Pre1 result2 Post2 Variant1 y0 z0
                                    Pre6 Pre5 Test2 y1 z1 Post6) y1 z1
                                    (refl_equal ? y1)
                                    (sqrt_po_8 x Pre7 Test5 Test3 result1
                                    Post1 Pre1 result2 Post2 Variant1 y0 z0
                                    Pre6 Pre5 Test2 y1 z1 Post6)) in
                                (exist_3 [y2: Z][z2: Z][result5: unit]
                                `z2 > 0` /\ `y2 > 0` /\
                                `z2 = (Zdiv ((Zdiv x y2) + y2) 2)` /\
                                `x < (y2 + 1) * (y2 + 1)` /\
                                `x < (z2 + 1) * (z2 + 1)` /\ `z2 >= y2` 
                                y1 z1 result4 Post5)
                            | (right Test1) =>
                                let (y1, z1, result4, Post5) =
                                  (exist_3 [y1: Z][z1: Z][result4: unit]
                                  `z1 > 0` /\ `y1 > 0` /\
                                  `z1 = (Zdiv ((Zdiv x y1) + y1) 2)` /\
                                  `x < (y1 + 1) * (y1 + 1)` /\
                                  `x < (z1 + 1) * (z1 + 1)` /\ `z1 >= y1` 
                                  y0 z0 tt
                                  (sqrt_po_9 x Pre7 Test5 Test3 result1 Post1
                                  Pre1 result2 Post2 Variant1 y0 z0 Pre6 Pre5
                                  Test1)) in
                                (exist_3 [y2: Z][z2: Z][result5: unit]
                                `z2 > 0` /\ `y2 > 0` /\
                                `z2 = (Zdiv ((Zdiv x y2) + y2) 2)` /\
                                `x < (y2 + 1) * (y2 + 1)` /\
                                `x < (z2 + 1) * (z2 + 1)` /\ `z2 >= y2` 
                                y1 z1 result4 Post5) end) result1 result1
                          result2 (refl_equal ? result1)
                          (sqrt_po_10 x Pre7 Test5 Test3 result1 Post1 Pre1
                          result2 Post2)) in
                      let (result4, Post17) = (exist_1 [result4: Z]
                        `result4 * result4 <= x` /\
                        `x < (result4 + 1) * (result4 + 1)` y0
                        (sqrt_po_11 x Pre7 Test5 Test3 result1 Post1 Pre1
                        result2 Post2 y0 z0 Post5)) in
                      (exist_3 [y1: Z][z1: Z][result5: Z]
                      `result5 * result5 <= x` /\
                      `x < (result5 + 1) * (result5 + 1)` y0 z0 result4
                      Post17) in
                    (exist_2 [y1: Z][result4: Z]`result4 * result4 <= x` /\
                    `x < (result4 + 1) * (result4 + 1)` y0 result3 Post15) in
                  (exist_1 [result3: Z]`result3 * result3 <= x` /\
                  `x < (result3 + 1) * (result3 + 1)` result2 Post14) in
                (exist_1 [result2: Z]`result2 * result2 <= x` /\
                `x < (result2 + 1) * (result2 + 1)` result1 Post13) end) in
          (exist_1 [result1: Z]`result1 * result1 <= x` /\
          `x < (result1 + 1) * (result1 + 1)` result0 Post11) end) in
    (exist_1 [result0: Z]`result0 * result0 <= x` /\
    `x < (result0 + 1) * (result0 + 1)` result Post9).

