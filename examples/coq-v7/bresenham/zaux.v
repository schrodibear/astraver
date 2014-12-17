(**************************************************************************)
(*                                                                        *)
(* Proof of the Bresenham line drawing algorithm.                         *)
(*                                                                        *)
(* Jean-Christophe Filliâtre (LRI, Université Paris Sud)                  *)
(* May 2001                                                               *)
(*                                                                        *)
(**************************************************************************)

(*s Some lemmas about absolute value (over type [Z]). *)

Require ZArith.
Require Omega.
Require ZArithRing.

(*s First a tactic [Case_Zabs] to do case split over [(Zabs x)]: 
    introduces two subgoals, one where [x] is assumed to be non negative
    and thus where [Zabs x] is replaced by [x]; and another where
    [x] is assumed to be non positive and thus where [Zabs x] is
    replaced by [-x]. *)

Lemma Z_gt_le : (x,y:Z)`x > y` -> `y <= x`.
Proof.
Intros; Omega.
Save.

Tactic Definition Case_Zabs a Ha := 
  Elim (Z_le_gt_dec ZERO a); Intro Ha; 
  [ Rewrite (Zabs_eq a Ha) 
  | Rewrite (Zabs_non_eq a (Z_gt_le ZERO a Ha)) ].

(*s A useful lemma to establish $|a| \le |b|$. *)

Lemma Zabs_le_Zabs : 
  (a,b:Z)(`b <= a <= 0` \/ `0 <= a <= b`) -> `|a| <= |b|`.
Proof.
Intro a; Case_Zabs a Ha; Intro b; Case_Zabs b Hb; Omega.
Save.

(*s A useful lemma to establish $|a| \le $. *)

Lemma Zabs_le : (a,b:Z) `0 <= b` -> `-b <= a <= b` <-> `|a| <= b`.
Proof.
Intros a b Hb. Case_Zabs a Ha; Split; Omega.
Save.

(*s Two tactics. [ZCompare x y H] discriminates between [x<y], [x=y] and 
    [x>y] ([H] is the hypothesis name). [RingSimpl x y] rewrites [x] by [y]
    using the [Ring] tactic. *)

Tactic Definition ZCompare x y H :=
  Elim (Z_gt_le_dec x y); Intro H; 
  [ Idtac | Elim (Z_le_lt_eq_dec x y H); Clear H; Intro H ].

Tactic Definition RingSimpl x y :=
  Replace x with y; [ Idtac | Ring ].

(*s Key lemma for Bresenham's proof: if [b] is at distance less or equal 
    than [1/2] from the rational [c/a], then it is the closest such integer.
    We express this property in [Z], thus multiplying everything by [2a]. *)

Lemma closest : 
  (a,b,c:Z) 
     `0 <= a`
  -> `|2*a*b - 2*c| <= a` 
  -> (b':Z) `|a*b - c| <= |a*b' - c|`.
Proof.
Intros a b c Ha Hmin.
Generalize (proj2 ? ? (Zabs_le `2*a*b-2*c` a Ha) Hmin).
Intros Hmin' b'.
Elim (Z_le_gt_dec `2*a*b` `2*c`); Intro Habc.
(* 2ab <= 2c *)
Rewrite (Zabs_non_eq `a*b-c`).
ZCompare b b' Hbb'.
  (* b > b' *)
  Rewrite (Zabs_non_eq `a*b'-c`).
  Apply Zle_left_rev.
  RingSimpl '`(-(a*b'-c))+(-(-(a*b-c)))` '`a*(b-b')`.
  Apply Zle_ZERO_mult; Omega.
  Apply Zge_le.
  Apply Zge_trans with m := `a*b-c`.
  Apply Zge_mult_simpl with c := `2`. Omega.
  RingSimpl '`0*2` '`0`. 
  RingSimpl '`(a*b-c)*2` '`2*a*b-2*c`. Omega.
  RingSimpl '`a*b'-c` '`a*b'+(-c)`.
  RingSimpl '`a*b-c` '`a*b+(-c)`.
  Apply Zle_ge.  
  Apply Zle_reg_r.
  Apply Zle_Zmult_pos_left; Omega.
  (* b < b' *)
  Rewrite (Zabs_eq `a*b'-c`).
  Apply Zle_mult_simpl with c := `2`. Omega.
  RingSimpl '`(a*b'-c)*2` '`2*(a*b'-a*b)+2*(a*b-c)`.
  Apply Zle_trans with `a`. 
  RingSimpl '`(-(a*b-c))*2` '`-(2*a*b-2*c)`. Omega.
  Apply Zle_trans with `2*a+(-a)`. Omega.
  Apply Zle_plus_plus.
  RingSimpl '`2*a` '`2*a*1`.
  RingSimpl '`2*(a*b'-a*b)` '`2*a*(b'-b)`.
  Apply Zle_Zmult_pos_left; Omega.
  RingSimpl '`2*(a*b-c)` '`2*a*b-2*c`. Omega.
    (* 0 <= ab'-c *)
    RingSimpl '`a*b'-c` '`(a*b'-a*b)+(a*b-c)`.
    RingSimpl '`0` '`a+(-a)`.
    Apply Zle_plus_plus.
    RingSimpl '`a` '`a*1`.
    RingSimpl '`a*1*b'-a*1*b` '`a*(b'-b)`.
    Apply Zle_Zmult_pos_left; Omega.
    Apply Zle_mult_simpl with c := `2`. Omega.
    Apply Zle_trans with `-a`. Omega.  
    RingSimpl '`(a*b-c)*2` '`2*a*b-2*c`. Omega.
  (* b = b' *)
  Rewrite <- Hbb'.
  Rewrite (Zabs_non_eq `a*b-c`). Omega.
  Apply Zge_le.
  Apply Zge_mult_simpl with c := `2`. Omega.
  RingSimpl '`0*2` '`0`. 
  RingSimpl '`(a*b-c)*2` '`2*a*b-2*c`. Omega. 
  Apply Zge_le.
  Apply Zge_mult_simpl with c := `2`. Omega.
  RingSimpl '`0*2` '`0`. 
  RingSimpl '`(a*b-c)*2` '`2*a*b-2*c`. Omega. 

(* 2ab > 2c *)
Rewrite (Zabs_eq `a*b-c`).
ZCompare b b' Hbb'.
  (* b > b' *)
  Rewrite (Zabs_non_eq `a*b'-c`).
  Apply Zle_mult_simpl with c := `2`. Omega.
  RingSimpl '`(-(a*b'-c))*2` '`2*(c-a*b)+2*(a*b-a*b')`.
  Apply Zle_trans with `a`. 
  RingSimpl '`(a*b-c)*2` '`2*a*b-2*c`. Omega.
  Apply Zle_trans with `(-a)+2*a`. Omega.
  Apply Zle_plus_plus.
  RingSimpl '`2*(c-a*b)` '`2*c-2*a*b`. Omega.
  RingSimpl '`2*a` '`2*a*1`.
  RingSimpl '`2*(a*b-a*b')` '`2*a*(b-b')`.
  Apply Zle_Zmult_pos_left; Omega.
    (* 0 >= ab'-c *)
    RingSimpl '`a*b'-c` '`(a*b'-a*b)+(a*b-c)`.
    RingSimpl '`0` '`(-a)+a`.
    Apply Zle_plus_plus.
    RingSimpl '`-a` '`a*(-1)`.
    RingSimpl '`a*b'-a*b` '`a*(b'-b)`.
    Apply Zle_Zmult_pos_left; Omega.
    Apply Zle_mult_simpl with c := `2`. Omega.
    Apply Zle_trans with `a`.
    RingSimpl '`(a*b-c)*2` '`2*a*b-2*c`.
    Omega. Omega.
  (* b < b' *)
  Rewrite (Zabs_eq `a*b'-c`).
  Apply Zle_left_rev.
  RingSimpl '`a*b'-c+(-(a*b-c))` '`a*(b'-b)`.
  Apply Zle_ZERO_mult; Omega.
  Apply Zle_trans with m := `a*b-c`.
  Apply Zle_mult_simpl with c := `2`. Omega.
  RingSimpl '`0*2` '`0`. 
  RingSimpl '`(a*b-c)*2` '`2*a*b-2*c`. Omega.
  RingSimpl '`a*b'-c` '`a*b'+(-c)`.
  RingSimpl '`a*b-c` '`a*b+(-c)`.
  Apply Zle_reg_r.
  Apply Zle_Zmult_pos_left; Omega.
  (* b = b' *)
  Rewrite <- Hbb'.  
  Rewrite (Zabs_eq `a*b-c`). Omega.
  Apply Zle_mult_simpl with c := `2`. Omega.
  RingSimpl '`0*2` '`0`. 
  RingSimpl '`(a*b-c)*2` '`2*a*b-2*c`. Omega. 
  Apply Zle_mult_simpl with c := `2`. Omega.
  RingSimpl '`0*2` '`0`. 
  RingSimpl '`(a*b-c)*2` '`2*a*b-2*c`. Omega. 
Save.
