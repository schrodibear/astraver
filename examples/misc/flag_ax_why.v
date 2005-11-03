(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.



(*Why type*) Parameter color: Set.

(*Why logic*) Definition blue : color.
Admitted.

(*Why logic*) Definition white : color.
Admitted.

(*Why logic*) Definition red : color.
Admitted.

(*Why predicate*) Definition is_color  (c:color)
  := c = blue \/ c = white \/ c = red.

(*Why*) Parameter eq_color :
  forall (c1: color), forall (c2: color),
  (sig_1 bool
   (fun (result: bool)  => ((if result then c1 = c2 else ~(c1 = c2))))).



(*Why type*) Parameter color_array: Set.

(*Why logic*) Definition acc : color_array -> Z -> color.
Admitted.

(*Why logic*) Definition upd : color_array -> Z -> color -> color_array.
Admitted.

(*Why logic*) Definition length : color_array -> Z.
Admitted.

(*Why axiom*) Lemma acc_upd_eq :
  (forall (a:color_array),
   (forall (i:Z), (forall (c:color), (acc (upd a i c) i) = c))).
Admitted.

(*Why axiom*) Lemma acc_upd_neq :
  (forall (a:color_array),
   (forall (i:Z),
    (forall (j:Z),
     (forall (c:color), (i <> j -> (acc (upd a j c) i) = (acc a i)))))).
Admitted.

(*Why axiom*) Lemma length_update :
  (forall (a:color_array),
   (forall (i:Z), (forall (c:color), (length (upd a i c)) = (length a)))).
Admitted.

(*Why*) Parameter get :
  forall (i: Z), forall (t: color_array), forall (_: 0 <= i /\ i <
  (length t)), (sig_1 color (fun (result: color)  => (result = (acc t i)))).

(*Why*) Parameter set :
  forall (i: Z), forall (c: color), forall (t: color_array), forall (_: 0 <=
  i /\ i < (length t)),
  (sig_2 color_array unit
   (fun (t0: color_array) (result: unit)  => (t0 = (upd t i c)))).

(*Why predicate*) Definition monochrome  (t:color_array) (i:Z) (j:Z)
  (c:color) := (forall (k:Z), (i <= k /\ k < j -> (acc t k) = c)).

(* Why obligation from file "flag_ax.mlw", line 0, characters 0-0: *)
Lemma swap_po_1 : 
  forall (i: Z),
  forall (j: Z),
  forall (t: color_array),
  forall (HW_1: (0 <= i /\ i < (length t)) /\ 0 <= j /\ j < (length t)),
  forall (result: color),
  forall (HW_2: result = (acc t i)),
  forall (result0: color),
  forall (HW_3: result0 = (acc t j)),
  forall (t0: color_array),
  forall (HW_4: t0 = (upd t i result0)),
  forall (t1: color_array),
  forall (HW_5: t1 = (upd t0 j result)),
  t1 = (upd (upd t i (acc t j)) j (acc t i)).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "flag_ax.mlw", line 0, characters 0-0: *)
Lemma swap_po_2 : 
  forall (i: Z),
  forall (j: Z),
  forall (t: color_array),
  forall (HW_1: (0 <= i /\ i < (length t)) /\ 0 <= j /\ j < (length t)),
  forall (result: color),
  forall (HW_2: result = (acc t i)),
  forall (result0: color),
  forall (HW_3: result0 = (acc t j)),
  forall (t0: color_array),
  forall (HW_4: t0 = (upd t i result0)),
  0 <= j /\ j < (length t0).
Proof.
intuition; subst.
rewrite length_update; intuition.
Save.

(* Why obligation from file "flag_ax.mlw", line 0, characters 0-0: *)
Lemma dutch_flag_po_1 : 
  forall (n: Z),
  forall (t: color_array),
  forall (HW_1: 0 <= n /\ (length t) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t k))))),
  (0 <= 0 /\ 0 <= 0) /\ (0 <= n /\ n <= n) /\ (monochrome t 0 0 blue) /\
  (monochrome t 0 0 white) /\ (monochrome t n n red) /\ (length t) = n /\
  (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t k)))).
Proof.
unfold monochrome; intuition.
absurd (0<0); intuition.
absurd (0<0); intuition.
absurd (n<n); intuition.
Save.

(* Why obligation from file "flag_ax.mlw", line 0, characters 0-0: *)
Lemma dutch_flag_po_2 : 
  forall (n: Z),
  forall (t: color_array),
  forall (HW_1: 0 <= n /\ (length t) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t k))))),
  forall (b: Z),
  forall (i: Z),
  forall (r: Z),
  forall (t0: color_array),
  forall (HW_2: (0 <= b /\ b <= i) /\ (i <= r /\ r <= n) /\
                (monochrome t0 0 b blue) /\ (monochrome t0 b i white) /\
                (monochrome t0 r n red) /\ (length t0) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t0 k))))),
  forall (HW_3: i < r),
  forall (result: color),
  forall (HW_4: result = (acc t0 i)),
  forall (HW_5: result = blue),
  forall (t1: color_array),
  forall (HW_6: t1 = (upd (upd t0 b (acc t0 i)) i (acc t0 b))),
  forall (b0: Z),
  forall (HW_7: b0 = (b + 1)),
  forall (i0: Z),
  forall (HW_8: i0 = (i + 1)),
  ((0 <= b0 /\ b0 <= i0) /\ (i0 <= r /\ r <= n) /\
  (monochrome t1 0 b0 blue) /\ (monochrome t1 b0 i0 white) /\
  (monochrome t1 r n red) /\ (length t1) = n /\
  (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t1 k))))) /\
  (Zwf 0 (r - i0) (r - i)).
Proof.
unfold monochrome; intuition; subst.
assert (k<b \/ k=b). omega. intuition.
do 2 (rewrite acc_upd_neq; intuition).
subst.
assert (b<i \/ b=i). omega. intuition.
rewrite acc_upd_neq; intuition.
rewrite acc_upd_eq; intuition.
subst.
rewrite acc_upd_eq; intuition.
assert (k<i \/ k=i). omega. intuition.
do 2 (rewrite acc_upd_neq; intuition).
subst.
rewrite acc_upd_eq; intuition.
do 2 (rewrite acc_upd_neq; intuition).
do 2 rewrite length_update; trivial.
assert (k<>i \/ k=i). omega. intuition.
rewrite acc_upd_neq; intuition.
assert (k<>b \/ k=b). omega. intuition.
rewrite acc_upd_neq; intuition.
subst; rewrite acc_upd_eq; intuition.
subst; rewrite acc_upd_eq; intuition.
Save.

(* Why obligation from file "flag_ax.mlw", line 0, characters 0-0: *)
Lemma dutch_flag_po_3 : 
  forall (n: Z),
  forall (t: color_array),
  forall (HW_1: 0 <= n /\ (length t) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t k))))),
  forall (b: Z),
  forall (i: Z),
  forall (r: Z),
  forall (t0: color_array),
  forall (HW_2: (0 <= b /\ b <= i) /\ (i <= r /\ r <= n) /\
                (monochrome t0 0 b blue) /\ (monochrome t0 b i white) /\
                (monochrome t0 r n red) /\ (length t0) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t0 k))))),
  forall (HW_3: i < r),
  forall (result: color),
  forall (HW_4: result = (acc t0 i)),
  forall (HW_5: result = blue),
  (0 <= b /\ b < (length t0)) /\ 0 <= i /\ i < (length t0).
Proof.
intuition.
Save.

(* Why obligation from file "flag_ax.mlw", line 0, characters 0-0: *)
Lemma dutch_flag_po_4 : 
  forall (n: Z),
  forall (t: color_array),
  forall (HW_1: 0 <= n /\ (length t) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t k))))),
  forall (b: Z),
  forall (i: Z),
  forall (r: Z),
  forall (t0: color_array),
  forall (HW_2: (0 <= b /\ b <= i) /\ (i <= r /\ r <= n) /\
                (monochrome t0 0 b blue) /\ (monochrome t0 b i white) /\
                (monochrome t0 r n red) /\ (length t0) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t0 k))))),
  forall (HW_3: i < r),
  forall (result: color),
  forall (HW_4: result = (acc t0 i)),
  forall (HW_9: ~(result = blue)),
  forall (result0: color),
  forall (HW_10: result0 = (acc t0 i)),
  forall (HW_11: result0 = white),
  forall (i0: Z),
  forall (HW_12: i0 = (i + 1)),
  ((0 <= b /\ b <= i0) /\ (i0 <= r /\ r <= n) /\ (monochrome t0 0 b blue) /\
  (monochrome t0 b i0 white) /\ (monochrome t0 r n red) /\ (length t0) = n /\
  (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t0 k))))) /\
  (Zwf 0 (r - i0) (r - i)).
Proof.
unfold monochrome; intuition; subst.
assert (k<i \/ k=i). omega. intuition.
subst; intuition.
Save.

(* Why obligation from file "flag_ax.mlw", line 0, characters 0-0: *)
Lemma dutch_flag_po_5 : 
  forall (n: Z),
  forall (t: color_array),
  forall (HW_1: 0 <= n /\ (length t) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t k))))),
  forall (b: Z),
  forall (i: Z),
  forall (r: Z),
  forall (t0: color_array),
  forall (HW_2: (0 <= b /\ b <= i) /\ (i <= r /\ r <= n) /\
                (monochrome t0 0 b blue) /\ (monochrome t0 b i white) /\
                (monochrome t0 r n red) /\ (length t0) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t0 k))))),
  forall (HW_3: i < r),
  forall (result: color),
  forall (HW_4: result = (acc t0 i)),
  forall (HW_9: ~(result = blue)),
  forall (result0: color),
  forall (HW_10: result0 = (acc t0 i)),
  forall (HW_13: ~(result0 = white)),
  forall (r0: Z),
  forall (HW_14: r0 = (r - 1)),
  forall (t1: color_array),
  forall (HW_15: t1 = (upd (upd t0 r0 (acc t0 i)) i (acc t0 r0))),
  ((0 <= b /\ b <= i) /\ (i <= r0 /\ r0 <= n) /\ (monochrome t1 0 b blue) /\
  (monochrome t1 b i white) /\ (monochrome t1 r0 n red) /\ (length t1) = n /\
  (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t1 k))))) /\
  (Zwf 0 (r0 - i) (r - i)).
Proof.
unfold monochrome; intuition; subst.
do 2 (rewrite acc_upd_neq; intuition).
do 2 (rewrite acc_upd_neq; intuition).
assert (k=i \/ i <k). omega. intuition.
subst; rewrite acc_upd_eq; intuition.
assert (i=r-1). omega. subst.
assert (h:0 <= r-1 < length t). omega.
generalize (H11 (r-1) h); unfold is_color; intuition.
rewrite acc_upd_neq; intuition.
assert (k=r-1 \/ r-1<k). omega. intuition.
subst; rewrite acc_upd_eq; intuition.
assert (h:0 <= i < length t). omega.
generalize (H11 i h); unfold is_color; intuition.
rewrite acc_upd_neq; intuition.
do 2 rewrite length_update; trivial.
assert (k<>i \/ k=i). omega. intuition.
rewrite acc_upd_neq; intuition.
assert (k<>r-1 \/ k=r-1). omega. intuition.
rewrite acc_upd_neq; intuition.
subst; rewrite acc_upd_eq; intuition.
subst; rewrite acc_upd_eq; intuition.
Save.

(* Why obligation from file "flag_ax.mlw", line 0, characters 0-0: *)
Lemma dutch_flag_po_6 : 
  forall (n: Z),
  forall (t: color_array),
  forall (HW_1: 0 <= n /\ (length t) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t k))))),
  forall (b: Z),
  forall (i: Z),
  forall (r: Z),
  forall (t0: color_array),
  forall (HW_2: (0 <= b /\ b <= i) /\ (i <= r /\ r <= n) /\
                (monochrome t0 0 b blue) /\ (monochrome t0 b i white) /\
                (monochrome t0 r n red) /\ (length t0) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t0 k))))),
  forall (HW_3: i < r),
  forall (result: color),
  forall (HW_4: result = (acc t0 i)),
  forall (HW_9: ~(result = blue)),
  forall (result0: color),
  forall (HW_10: result0 = (acc t0 i)),
  forall (HW_13: ~(result0 = white)),
  forall (r0: Z),
  forall (HW_14: r0 = (r - 1)),
  (0 <= r0 /\ r0 < (length t0)) /\ 0 <= i /\ i < (length t0).
Proof.
intuition.
Save.

(* Why obligation from file "flag_ax.mlw", line 0, characters 0-0: *)
Lemma dutch_flag_po_7 : 
  forall (n: Z),
  forall (t: color_array),
  forall (HW_1: 0 <= n /\ (length t) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t k))))),
  forall (b: Z),
  forall (i: Z),
  forall (r: Z),
  forall (t0: color_array),
  forall (HW_2: (0 <= b /\ b <= i) /\ (i <= r /\ r <= n) /\
                (monochrome t0 0 b blue) /\ (monochrome t0 b i white) /\
                (monochrome t0 r n red) /\ (length t0) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t0 k))))),
  forall (HW_3: i < r),
  forall (result: color),
  forall (HW_4: result = (acc t0 i)),
  forall (HW_9: ~(result = blue)),
  0 <= i /\ i < (length t0).
Proof.
intuition.
Save.

(* Why obligation from file "flag_ax.mlw", line 0, characters 0-0: *)
Lemma dutch_flag_po_8 : 
  forall (n: Z),
  forall (t: color_array),
  forall (HW_1: 0 <= n /\ (length t) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t k))))),
  forall (b: Z),
  forall (i: Z),
  forall (r: Z),
  forall (t0: color_array),
  forall (HW_2: (0 <= b /\ b <= i) /\ (i <= r /\ r <= n) /\
                (monochrome t0 0 b blue) /\ (monochrome t0 b i white) /\
                (monochrome t0 r n red) /\ (length t0) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t0 k))))),
  forall (HW_3: i < r),
  0 <= i /\ i < (length t0).
Proof.
intuition.
Save.

(* Why obligation from file "flag_ax.mlw", line 0, characters 0-0: *)
Lemma dutch_flag_po_9 : 
  forall (n: Z),
  forall (t: color_array),
  forall (HW_1: 0 <= n /\ (length t) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t k))))),
  forall (b: Z),
  forall (i: Z),
  forall (r: Z),
  forall (t0: color_array),
  forall (HW_2: (0 <= b /\ b <= i) /\ (i <= r /\ r <= n) /\
                (monochrome t0 0 b blue) /\ (monochrome t0 b i white) /\
                (monochrome t0 r n red) /\ (length t0) = n /\
                (forall (k:Z), (0 <= k /\ k < n -> (is_color (acc t0 k))))),
  forall (HW_16: i >= r),
  (exists b:Z,
   (exists r:Z, (monochrome t0 0 b blue) /\ (monochrome t0 b r white) /\
    (monochrome t0 r n red))).
Proof.
intros.
exists b; exists r; intuition.
assert (i=r). omega. subst; intuition.
Save.

