
(*s Axiomatization of words over a alphabet [A]. *)

Require PolyList.
Require ZArith.
Require ZArithRing.
Require WhyArrays.
Require ProgWf.
Require Omega.

(*s Alphabet. This is an abstract type [A] where equality is decidable.*)

Parameter A:Set.
 
Axiom A_eq_dec : (a,b:A) { a=b }+{ ~a=b }.

(*s Words are list of characters. *)

Definition word := (list A).
Definition eps := (nil A).

Definition concat := app.
Implicits concat [1].


(*s Distance. It is axiomatized as a predicate [dist w1 w2 n] expressing that
    [w1] and [w2] are at distance at most [n] (i.e. there exists a path of 
    length [n] from [w1] to [w2]). *)

Inductive dist : word -> word -> Z -> Prop :=
  dist_eps :
    (dist eps eps `0`)
| dist_add_left : 
    (w1,w2:word)(n:Z) (dist w1 w2 n) -> (a:A) (dist (cons a w1) w2 `n+1`)
| dist_add_right : 
    (w1,w2:word)(n:Z) (dist w1 w2 n) -> (a:A) (dist w1 (cons a w2) `n+1`)
| dist_context :
    (w1,w2:word)(n:Z) (dist w1 w2 n) -> (a:A) (dist (cons a w1) (cons a w2) n).

(*s Then we introducve the minimal distance between two words. *)

Definition min_dist := 
  [w1,w2:word][n:Z] (dist w1 w2 n) /\ ((m:Z)(dist w1 w2 m) -> `n <= m`).


(*s Length of a word (in type [Z]). *)

Fixpoint Zlength [w:word] : Z :=
  Cases w of
    nil => `0`
  | (cons _ w') => `(Zlength w')+1`
end.


(*s Auxiliary result on words:
    Any word [au] starting with a character can be written as a
    word [vb] ending with a character. *)

Fixpoint last_char [a:A][u:word] : A :=
  Cases u of
    nil => a
  | (cons c u') => (last_char c u') end.

Fixpoint but_last [a:A][u:word] : word := 
  Cases u of
    nil => eps
  | (cons c u') => (cons a (but_last c u')) end.

Lemma first_last_explicit : 
  (u:word)(a:A)
    (concat (but_last a u) (cons (last_char a u) eps))=(cons a u).
Proof.
Induction u; Simpl.
Reflexivity.
Intros.
Rewrite (H a).
Reflexivity.
Save.

Lemma first_last : 
  (a:A)(u:word)
  (EX v | (EX b | (concat v (cons b eps))=(cons a u)
               /\ (Zlength v)=(Zlength u))).
Proof.
Intros a u.
Exists (but_last a u).
Exists (last_char a u).
Split. Exact (first_last_explicit u a).
Generalize a; Induction u; Simpl; Intros.
Omega.
Generalize (Hrecu a0); Intros; Omega.
Save.


(*s Key lemma: if [dist w1 aw2 n] then there exists [u1], [v1],
    [k] such that [dist v1 w2 k], [w1=u1v1] and [k+(length u1)-1<=m]. *)

Lemma key_lemma_right :
  (w1,w'2:word)(m:Z)(a:A)
  (dist w1 w'2 m) -> 
  (w2:word) w'2=(cons a w2) ->
  (EX u1 | (EX v1 | (EX k |
     w1 = (concat u1 v1) /\ (dist v1 w2 k) 
  /\ `k + (Zlength u1) <= m + 1`))).
Proof.
Intros w1 w'2 m a H; Elim H.
(* 1. [dist_eps]: absurd *)
Intros; Discriminate H0.
(* 2. [dist_add_left]: we use induction hypothesis. *)
Intros w'1 w3 n Hdist Hrec b w2 Heq.  
Elim (Hrec w2 Heq); Intros u'1 Hex.
Elim Hex; Clear Hex; Intros v'1 Hex.
Elim Hex; Clear Hex; Intros k Hex.
Decompose [and] Hex; Clear Hex.
Elim (first_last b u'1); Intros u1 Hex.
Elim Hex; Intros c [ Hc Hlength ].
Exists u1; Exists (cons c v'1); Exists `k+1`.
Repeat Split.
Rewrite H0.
Rewrite app_comm_cons.
Rewrite <- Hc.
Rewrite app_ass; Reflexivity.
Apply dist_add_left; Assumption.
Omega.
(* 3. [dist_add_right]: direct *)
Intros.
Exists eps; Exists w0; Exists n.
Repeat Split.
Inversion H2.
Rewrite <- H5; Assumption.
Simpl; Omega.
(* 4. [dist_context]: direct *)
Intros.
Inversion H2.
Exists (cons a eps); Exists w0; Exists n.
Repeat Split.
Rewrite <- H5; Assumption.
Simpl; Omega.
Save.


(*s To get the symmetric key lemma, we use the symmetry of [dist]. *)

Lemma dist_symetry : 
  (w1,w2:word)(n:Z) (dist w1 w2 n) -> (dist w2 w1 n).
Proof.
Induction 1; Intros.
Exact dist_eps.
Apply dist_add_right; Assumption.
Apply dist_add_left; Assumption.
Apply dist_context; Assumption.
Save.

Lemma key_lemma_left :
  (w1,w2:word)(m:Z)(a:A)
  (dist (cons a w1) w2 m) -> 
  (EX u2 | (EX v2 | (EX k |
     w2 = (concat u2 v2) /\ (dist w1 v2 k) 
  /\ `k + (Zlength u2) <= m + 1`))).
Proof.
Intros w1 w2 m a Hdist.
Generalize (dist_symetry (cons a w1) w2 m Hdist); Intro Hrev.

Elim (key_lemma_right w2 (cons a w1) m a Hrev w1).
Intros u2 Hex; Elim Hex; Clear Hex.
Intros v2 Hex; Elim Hex; Clear Hex.
Intros k Hex.
Decompose [and] Hex; Clear Hex.
Exists u2.
Exists v2.
Exists k.
Repeat Split; Try Assumption.
Apply dist_symetry; Assumption.
Reflexivity.
Save.


(*s Concatenation to the left: if [dist w1 w2 n] then
    [dist uw1 w2 (|u|+n)] and [dist w1 uw2 (|u|+n)]. *)

Lemma dist_concat_left :
  (u,v,w:word)(n:Z)
  (dist v w n) -> (dist (concat u v) w `(Zlength u)+n`).
Proof.
Induction u; Simpl; Intros.
Auto.
Replace `(Zlength l)+1+n` with `((Zlength l)+n)+1`; [ Idtac | Omega ].
Apply dist_add_left; Auto.
Save.

Lemma dist_concat_right :
  (u,v,w:word)(n:Z)
  (dist v w n) -> (dist v (concat u w) `(Zlength u)+n`).
Proof.
Induction u; Simpl; Intros.
Auto.
Replace `(Zlength l)+1+n` with `((Zlength l)+n)+1`; [ Idtac | Omega ].
Apply dist_add_right; Auto.
Save.


(*s First main lemma for correctness: [d(aw1,aw2)=d(w1,w2)]. *)

Lemma min_dist_equal : 
  (w1,w2:word)(a:A)(n:Z)
  (min_dist w1 w2 n) ->
  (min_dist (cons a w1) (cons a w2) n).
Proof.
Intros w1 w2 a n.
Unfold min_dist.
Generalize dist_context;Intuition.

Inversion H0.

Elim (key_lemma_right w1 (cons a w2) n0 a H7 w2); [ Idtac | Reflexivity ].
Intros u1 Hex; Elim Hex; Clear Hex.
Intros v1 Hex; Elim Hex; Clear Hex.
Intros k Hex. Decompose [and] Hex; Clear Hex.
Generalize (dist_concat_left u1 v1 w2 k H10); Intro.
Apply Zle_trans with `(Zlength u1)+k`.
Apply H2.
Rewrite H8; Assumption.
Omega.
Elim (key_lemma_left w1 w2 n0 a H7).
Intros u2 Hex; Elim Hex; Clear Hex.
Intros v2 Hex; Elim Hex; Clear Hex.
Intros k Hex. Decompose [and] Hex; Clear Hex.
Generalize (dist_concat_right u2 w1 v2 k H10); Intro.
Apply Zle_trans with `(Zlength u2)+k`.
Apply H2.
Rewrite H8; Assumption.
Omega.
Auto.
Save.


(*s Second main lemma for correctness: \par\noindent
    if [~a=b], then [d(aw1,bw2)=1+min(d(aw1,w2),d(w1,bw2))]. *)

Lemma min_dist_diff :
  (w1,w2:word)(a,b:A)(m,p:Z)
  ~a=b ->
  (min_dist (cons a w1) w2          p) ->
  (min_dist w1          (cons b w2) m) ->
  (min_dist (cons a w1) (cons b w2) `(Zmin m p)+1`). 
Proof.
Intros w1 w2 a b m p. Unfold min_dist; Intuition.
Unfold Zmin.
Case (Zcompare m p); Generalize dist_add_left dist_add_right; Intuition.

Generalize (Zle_min_l m p) (Zle_min_r m p) Zle_reg_r Zle_trans.
Inversion H1; Intuition EAuto.
Save.

(*s Two trivial lemmas needed for correctness. *)

Lemma min_dist_eps : 
  (w:word)(a:A)(n:Z)
  (min_dist w eps n) -> (min_dist (cons a w) eps `n+1`).
 Proof.
Unfold min_dist.
Intros w a n [H1 H2]. Split.
Apply dist_add_left.
Assumption.
Intros m Hm; Inversion Hm.
Generalize (H2 n0 H5).
Intros; Omega.
Save.

Lemma min_dist_eps_length : (w:word)(min_dist eps w (Zlength w)).
Proof.
Intros w; Unfold min_dist; Intuition.
Induction w; Simpl; Intros.
Exact dist_eps.
Apply dist_add_right; Assumption.
Generalize m H. Clear m H.
Induction w; Intros m H; Inversion H; Simpl.
Omega.
Generalize (Hrecw n H4); Intro; Omega.
Save.


(*s Suffixes of an array of characters. 
    Given an array [t] of length [n] of characters, we define
    [suffix t i] as the word [t(i)t(i+1)...t(n-1)],
    by well-founded recursion over [n-i]. *)

Section suffixes.

Variable n:Z.
Variable t:(array n A).

Definition F : (i:Z)((j:Z)(Zwf_up n j i)->word)->word.
Proof.
Intros i f.
Elim (Z_lt_ge_dec i `0`); Intro Hi.
Exact eps.
Elim (Z_lt_ge_dec i n); Intro H1.
Refine (cons (access t i) (f `i+1` ?)).
Unfold Zwf_up; Omega.
Exact eps.
Defined.

Definition suffix := 
  (fix Z (Zwf_up n) (Zwf_up_well_founded n) [i:Z]word F).

(*s To use [fix_eq], we need to establish extensionality of [F]. *)

Lemma extensionality :   
  (x:Z; f,g:((y:Z)(Zwf_up n y x)->word))
    ((y:Z; p:(Zwf_up n y x))(f y p)=(g y p))->(F x f)=(F x g).
Proof.
Intros.
Unfold F.
Case (Z_lt_ge_dec x `0`); Simpl.
Auto.
Intro; Case (Z_lt_ge_dec x n); Simpl.
Intro. Apply (f_equal ? ? (cons (access t x))).
Apply H.
Auto.
Save.

(*s Induction case for [suffix]. *)

Lemma suffix_is_cons : 
  (i:Z)`0 <= i < n` ->
  (suffix i) = (cons (access t i) (suffix `i+1`)).
Proof.
Intros i Hi.
Rewrite (fix_eq Z (Zwf_up n) (Zwf_up_well_founded n) [i:Z]word F
         extensionality).
Unfold F.
Case (Z_lt_ge_dec i `0`).
Intros; Absurd `i < 0`; Omega.
Case (Z_lt_ge_dec i n).
Intros; Simpl.
Reflexivity.
Intros; Absurd `i >= n`; Omega.
Save.

(*s Base case: the empty suffix. *)

Lemma suffix_n_is_eps : (suffix n) = eps. 
Proof.
Rewrite (fix_eq Z (Zwf_up n) (Zwf_up_well_founded n) [i:Z]word F
         extensionality).
Unfold F.
Case (Z_lt_ge_dec n `0`).
Reflexivity.
Case (Z_lt_ge_dec n n).
Intros; Absurd `n < n`; Omega.
Reflexivity.
Save.

(*s The whole array as a word. *)

Definition word_of_array := (suffix `0`).

(*s Length of a suffix. *)

Lemma suffix_length : 
  (i:Z)`0 <= i <= n` -> `(Zlength (suffix i)) = n-i`.
Proof.
(* proof is by induction over [n-i] *)
Intros i Hi. Generalize Hi. 
Replace i with `n-(n-i)`.
Replace `n-(n-(n-i))` with `n-i`.
Pattern `n-i`; Apply natlike_ind.
(* base case *)
Intros; Replace `n-0` with n.
Rewrite suffix_n_is_eps; Reflexivity.
Omega.
(* induction case *)
Intros.
Rewrite suffix_is_cons; [ Idtac | Omega ].
Simpl.
Unfold Zs; Ring.
Replace `n-(1+x)+1` with `n-x`; [ Idtac | Ring ].
Apply H0; Omega.
Omega.
Omega.
Omega.
Save.

End suffixes.

Implicits suffix [1].
Implicits word_of_array [1].


(*s Bonus: we show the equivalence with another definition of the
    distance. *)

Inductive dist' : word -> word -> Z -> Prop :=
  dist'_eps :
    (dist' eps eps `0`)
| dist'_add_left : 
    (w1,w2:word)(n:Z) (dist' w1 w2 n) -> (a:A) (dist' (cons a w1) w2 `n+1`)
| dist'_add_right : 
    (w1,w2:word)(n:Z) (dist' w1 w2 n) -> (a:A) (dist' w1 (cons a w2) `n+1`)
| dist'_context :
    (w1,w2,u,v:word)(n:Z) 
    (dist' w1 w2 n) -> 
    (dist' (concat u (concat w1 v)) (concat u (concat w2 v)) n).

Lemma cons_is_concat :
  (w:word)(a:A)(cons a w)=(concat (cons a eps) (concat w eps)).
Proof.
Intros w a; Simpl.
Unfold concat; Unfold eps; Rewrite <- app_nil_end.
Reflexivity.
Save.

Lemma dist_is_dist' :
  (w1,w2:word)(n:Z)(dist w1 w2 n) -> (dist' w1 w2 n).
Proof.
Induction 1.
Exact dist'_eps.
Intros; Apply dist'_add_left; Assumption.
Intros; Apply dist'_add_right; Assumption.
Intros.
Rewrite (cons_is_concat w0 a).
Rewrite (cons_is_concat w3 a).
Apply dist'_context; Assumption.
Save.

Lemma dist_concat_both_left : 
  (n:Z)(u,w1,w2:word)
  (dist w1 w2 n) -> (dist (concat u w1) (concat u w2) n).
Proof.
Induction u; Simpl; Intros.
Auto.
Apply dist_context; Auto.
Save.

Lemma dist_concat_both_right : 
  (n:Z)(w1,w2:word)
  (dist w1 w2 n) -> (u:word)(dist (concat w1 u) (concat w2 u) n).
Proof.
Induction 1; Simpl; Intros.
Induction u; Simpl.
Exact dist_eps.
Apply dist_context; Assumption.
Apply dist_add_left. Exact (H1 u).
Apply dist_add_right. Exact (H1 u).
Apply dist_context. Exact (H1 u).
Save.

Lemma dist'_is_dist :
  (w1,w2:word)(n:Z)(dist' w1 w2 n) -> (dist w1 w2 n).
Proof.
Induction 1.
Exact dist_eps.
Intros; Apply dist_add_left; Assumption.
Intros; Apply dist_add_right; Assumption.
Intros.
Apply dist_concat_both_left.
Apply dist_concat_both_right.
Assumption.
Save.
