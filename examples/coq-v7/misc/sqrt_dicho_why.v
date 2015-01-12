(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

Lemma mean1 : (x,y:Z) `x<=y` -> `x <= (x+y)/2 `.
Proof.
Intros.
Assert `(x+y)/2 >= (x+x)/2`.
Apply Z_div_ge; Omega.
Assert `(x+x)/2 = x`; Auto with *.
Replace `x+x` with `0 + x*2`; Auto with *.
Rewrite (Z_div_plus `0` x `2`); Auto with *.
Save.

Lemma mean2 : (x,y:Z) `x<y` -> `(x+y)/2 < y`.
Proof.
Intros.
Apply (!Zlt_Zmult_right2 `(x+y)/2` `y` `2`).
Auto with *.
Replace `(x+y)/2*2` with `2*((x+y)/2)`; Auto with *.
Assert `2*((x+y)/2) <= x+y`.
Apply (Z_mult_div_ge `x+y` `2`).
Auto with *.
Omega.
Save.

Hints Resolve mean1 mean2.

(* Why obligation from file "sqrt_dicho.mlw", characters 326-346 *)
Lemma sqrt_po_1 : 
  (x: Z)
  (Pre5: `x >= 0`)
  (inf: Z)
  (Post7: inf = `0`)
  (sup: Z)
  (Post6: sup = `x + 1`)
  (mil: Z)
  (Post5: mil = `0`)
  (Variant1: Z)
  (inf1: Z)
  (sup1: Z)
  (Pre4: Variant1 = `sup1 - inf1`)
  (Pre3: `inf1 * inf1 <= x` /\ `x < sup1 * sup1` /\ `inf1 < sup1`)
  (Test4: `inf1 + 1 <> sup1`)
  ~(`2` = `0`).
Proof.
Intuition.
Save.

(* Why obligation from file "sqrt_dicho.mlw", characters 375-386 *)
Lemma sqrt_po_2 : 
  (x: Z)
  (Pre5: `x >= 0`)
  (inf: Z)
  (Post7: inf = `0`)
  (sup: Z)
  (Post6: sup = `x + 1`)
  (mil: Z)
  (Post5: mil = `0`)
  (Variant1: Z)
  (inf1: Z)
  (sup1: Z)
  (Pre4: Variant1 = `sup1 - inf1`)
  (Pre3: `inf1 * inf1 <= x` /\ `x < sup1 * sup1` /\ `inf1 < sup1`)
  (Test4: `inf1 + 1 <> sup1`)
  (Pre2: ~(`2` = `0`))
  (mil2: Z)
  (Post1: mil2 = (Zdiv (`inf1 + (sup1 + 1)`) `2`))
  (Test3: `x < mil2 * mil2`)
  (sup2: Z)
  (Post2: sup2 = mil2)
  (`inf1 * inf1 <= x` /\ `x < sup2 * sup2` /\ `inf1 < sup2`) /\
  (Zwf `0` `sup2 - inf1` `sup1 - inf1`).
Proof.
Intuition.
Subst sup2; Trivial.
Subst mil2 sup2.
Replace `inf1+(sup1+1)` with `(inf1+(sup1-1))+1*2`; Try Omega.
Rewrite Z_div_plus; Try Omega.
Assert `inf1 <= (inf1+(sup1-1))/2`.
Apply mean1; Omega.
Omega.
Unfold Zwf.
Split; Try Omega.
Subst mil2 sup2. 
Replace `inf1+(sup1+1)` with `(inf1+1)+sup1`; Try Omega.
Assert `((inf1+1)+sup1)/2 < sup1`.
Apply mean2; Omega.
Omega.
Save.

(* Why obligation from file "sqrt_dicho.mlw", characters 392-403 *)
Lemma sqrt_po_3 : 
  (x: Z)
  (Pre5: `x >= 0`)
  (inf: Z)
  (Post7: inf = `0`)
  (sup: Z)
  (Post6: sup = `x + 1`)
  (mil: Z)
  (Post5: mil = `0`)
  (Variant1: Z)
  (inf1: Z)
  (sup1: Z)
  (Pre4: Variant1 = `sup1 - inf1`)
  (Pre3: `inf1 * inf1 <= x` /\ `x < sup1 * sup1` /\ `inf1 < sup1`)
  (Test4: `inf1 + 1 <> sup1`)
  (Pre2: ~(`2` = `0`))
  (mil2: Z)
  (Post1: mil2 = (Zdiv (`inf1 + (sup1 + 1)`) `2`))
  (Test2: `x >= mil2 * mil2`)
  (inf2: Z)
  (Post3: inf2 = mil2)
  (`inf2 * inf2 <= x` /\ `x < sup1 * sup1` /\ `inf2 < sup1`) /\
  (Zwf `0` `sup1 - inf2` `sup1 - inf1`).
Proof.
Intuition.
Subst mil2 inf2; Omega.
Subst mil2 inf2.
Replace `inf1+(sup1+1)` with `(inf1+1)+sup1`; Try Omega.
Assert `((inf1+1)+sup1)/2 < sup1`.
Apply mean2; Omega.
Omega.
Unfold Zwf; Split; Try Omega.
Subst inf2 mil2.
Replace `inf1+(sup1+1)` with `(inf1+1)+sup1`; Try Omega.
Assert `inf1+1 <= ((inf1+1)+sup1)/2`.
Apply mean1; Omega.
Omega.
Save.

(* Why obligation from file "sqrt_dicho.mlw", characters 235-287 *)
Lemma sqrt_po_4 : 
  (x: Z)
  (Pre5: `x >= 0`)
  (inf: Z)
  (Post7: inf = `0`)
  (sup: Z)
  (Post6: sup = `x + 1`)
  (mil: Z)
  (Post5: mil = `0`)
  `inf * inf <= x` /\ `x < sup * sup` /\ `inf < sup`.
Proof.
Intuition.
Subst inf; Omega.
Subst sup.
Ring `(x+1)*(x+1)`.
Assert `0 <= x*x`.
Auto with *.
Omega.
Save.

(* Why obligation from file "sqrt_dicho.mlw", characters 412-416 *)
Lemma sqrt_po_5 : 
  (x: Z)
  (Pre5: `x >= 0`)
  (inf: Z)
  (Post7: inf = `0`)
  (sup: Z)
  (Post6: sup = `x + 1`)
  (mil: Z)
  (Post5: mil = `0`)
  (inf1: Z)
  (sup1: Z)
  (Post4: (`inf1 * inf1 <= x` /\ `x < sup1 * sup1` /\ `inf1 < sup1`) /\
          `inf1 + 1 = sup1`)
  `inf1 * inf1 <= x` /\ `x < (inf1 + 1) * (inf1 + 1)`.
Proof.
Intuition.
Rewrite H0; Assumption.
Save.

