(********************************************************************

  A simple algorithm for computing the square root of a non-negative
  integer.

  Proofs of obligations generated by Why.

  (c) Claude MarchÃ©, may 2002

**********************************************************************)

(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)


Require ZArith.
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

(* Why obligation from file "sqrt.mlw", characters 391-392 *)
Lemma sqrt_po_1 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test6: `x = 0`)
  `0 * 0 <= x` /\ `x < (0 + 1) * (0 + 1)`.
Proof. (* sqrt_po_1 *)
Auto with *.
Save.

(* Why obligation from file "sqrt.mlw", characters 417-418 *)
Lemma sqrt_po_2 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test4: `x <= 3`)
  `1 * 1 <= x` /\ `x < (1 + 1) * (1 + 1)`.
Proof. (* sqrt_po_2 *)
Auto with *.
Save.

(* Why obligation from file "sqrt.mlw", characters 460-467 *)
Lemma sqrt_po_3 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (y: Z)
  (Post5: y = x)
  ~(`2` = `0`).
Proof. (* sqrt_po_3 *)
Auto with *.
Save.

(* Why obligation from file "sqrt.mlw", characters 654-660 *)
Lemma sqrt_po_4 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (y: Z)
  (Post5: y = x)
  (Pre6: ~(`2` = `0`))
  (z: Z)
  (Post4: z = (Zdiv (`x + 1`) `2`))
  (Variant1: Z)
  (y1: Z)
  (z1: Z)
  (Pre5: Variant1 = y1)
  (Pre4: `z1 > 0` /\ `y1 > 0` /\ `z1 = (Zdiv ((Zdiv x y1) + y1) 2)` /\
         `x < (y1 + 1) * (y1 + 1)` /\ `x < (z1 + 1) * (z1 + 1)`)
  (Test2: `z1 < y1`)
  (y2: Z)
  (Post1: y2 = z1)
  (Pre2: ~(`2` = `0`))
  ~(z1 = `0`).
Proof. 
Intuition.
Save.


(* Why obligation from file "sqrt.mlw", characters 636-670 *)
Lemma sqrt_po_5 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (y: Z)
  (Post5: y = x)
  (Pre6: ~(`2` = `0`))
  (z: Z)
  (Post4: z = (Zdiv (`x + 1`) `2`))
  (Variant1: Z)
  (y1: Z)
  (z1: Z)
  (Pre5: Variant1 = y1)
  (Pre4: `z1 > 0` /\ `y1 > 0` /\ `z1 = (Zdiv ((Zdiv x y1) + y1) 2)` /\
         `x < (y1 + 1) * (y1 + 1)` /\ `x < (z1 + 1) * (z1 + 1)`)
  (Test2: `z1 < y1`)
  (y2: Z)
  (Post1: y2 = z1)
  (Pre2: ~(`2` = `0`))
  (Pre3: ~(z1 = `0`))
  (z2: Z)
  (Post2: z2 = (Zdiv (`(Zdiv x z1) + z1`) `2`))
  (`z2 > 0` /\ `y2 > 0` /\ `z2 = (Zdiv ((Zdiv x y2) + y2) 2)` /\
  `x < (y2 + 1) * (y2 + 1)` /\ `x < (z2 + 1) * (z2 + 1)`) /\ (Zwf `0` y2 y1).
Proof. 
Unfold Zwf; Intuition.
Subst z2.
Apply iter_sqrt_pos; Omega.
Subst y2; Assumption.
Subst y2; Assumption.
Apply (iter_sqrt_invar3 x z1); Auto.
Omega.
Save.

(* Why obligation from file "sqrt.mlw", characters 525-613 *)
Lemma sqrt_po_6 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (y: Z)
  (Post5: y = x)
  (Pre6: ~(`2` = `0`))
  (z: Z)
  (Post4: z = (Zdiv (`x + 1`) `2`))
  `z > 0` /\ `y > 0` /\ `z = (Zdiv ((Zdiv x y) + y) 2)` /\
  `x < (y + 1) * (y + 1)` /\ `x < (z + 1) * (z + 1)`.
Proof. 
(* sqrt_po_6 *)
Intuition.
Subst z.
Assert `(x+1)/2 >= 1`.
Pattern 2 `1`; Replace `1` with `2/2`; Trivial.
Apply Z_div_ge; Try Omega.
Omega.
Subst y.
Assert `x/x+x = x+1`.
Assert xPos:`x>0`; Try Omega.
Generalize (Z_div_same x xPos). 
Intro.
Rewrite H; Omega.
Rewrite H; Trivial.

Subst y.
Assert `(x+1)*(x+1) >= (x+1)*1`.
Apply Zge_Zmult_pos_left; Try Omega.
Assert `(x+1)*1 = x+1`; Try Ring.
Omega.

Subst z.
Apply (iter_sqrt_invar3 x x); Try Omega.
Assert `x/x+x = x+1`.
Assert xPos:`x>0`; Try Omega.
Generalize (Z_div_same x xPos). 
Intro.
Rewrite H; Omega.
Rewrite H; Trivial.
Save.

(* Why obligation from file "sqrt.mlw", characters 679-681 *)
Lemma sqrt_po_7 : 
  (x: Z)
  (Pre7: `x >= 0`)
  (Test5: `x <> 0`)
  (Test3: `x > 3`)
  (y: Z)
  (Post5: y = x)
  (Pre6: ~(`2` = `0`))
  (z: Z)
  (Post4: z = (Zdiv (`x + 1`) `2`))
  (y1: Z)
  (z1: Z)
  (Post3: (`z1 > 0` /\ `y1 > 0` /\ `z1 = (Zdiv ((Zdiv x y1) + y1) 2)` /\
          `x < (y1 + 1) * (y1 + 1)` /\ `x < (z1 + 1) * (z1 + 1)`) /\
          `z1 >= y1`)
  `y1 * y1 <= x` /\ `x < (y1 + 1) * (y1 + 1)`.
Proof.
Intuition.
Apply (iter_sqrt_invar4 x y1 z1); Try Omega.
Save.

