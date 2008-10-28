(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)
Require Export Why.

(*Why inductive*) Inductive isfib  : Z -> Z -> Prop 
  := | isfib0 : (isfib 0 0)
     
     | isfib1 : (isfib 1 1)
     
     | isfibn : (forall (n:Z),
                 (forall (p:Z),
                  (forall (q:Z),
                   (n >= 0 /\ (isfib n p) /\ (isfib (n + 1) q) ->
                    (isfib (n + 2) (p + q))))))
     .


Hint Constructors isfib.



(* Why obligation from file "inductive.mlw", line 7, characters 0-21: *)
(*Why goal*) Lemma fib0 : 
  (isfib 0 0).
Proof.
auto.
Save.

(* Why obligation from file "inductive.mlw", line 8, characters 0-21: *)
(*Why goal*) Lemma fib1 : 
  (isfib 1 1).
Proof.
auto.
Save.

(* Why obligation from file "inductive.mlw", line 9, characters 0-21: *)
(*Why goal*) Lemma fib2 : 
  (isfib 2 1).
Proof.
change (isfib(0+2)(0+1)).
apply isfibn; intuition.
Save.

(* Why obligation from file "inductive.mlw", line 10, characters 0-21: *)
(*Why goal*) Lemma fib6 : 
  (isfib 6 8).
Proof.
assert (fib3:isfib 3 2).
change (isfib(1+2)(1+1)).
apply isfibn; intuition.
apply fib2.
assert (fib4:isfib 4 3).
change (isfib(2+2)(1+2)).
apply isfibn; intuition.
apply fib2.
assert (fib5:isfib 5 5).
change (isfib(3+2)(2+3)).
apply isfibn; intuition.
change (isfib(4+2)(3+5)).
apply isfibn; intuition.
Save.

(* Why obligation from file "inductive.mlw", line 11, characters 0-29: *)
(*Why goal*) Lemma neg_fib2 : 
  ~(isfib 2 2).
Proof.
intro H.
inversion H.
assert (n=0) by omega.
subst; intuition.
inversion H2.
subst.
assert (q=2) by omega.
replace (0+1) with 1 in H5 by omega.
inversion H5.
omega.
intuition.
intuition.
Save.

(* Why obligation from file "inductive.mlw", line 12, characters 0-29: *)
(*Why goal*) Lemma neg_fib5 : 
  ~(isfib 5 6).
Proof.
Admitted.

(* Why obligation from file "inductive.mlw", line 18, characters 4-19: *)
(*Why goal*) Lemma fib_po_1 : 
  forall (n: Z),
  forall (HW_1: n >= 0),
  forall (HW_2: 0 <= n /\ n <= 1),
  (isfib n n).
Proof.
intros.
assert (n=0 \/ n=1).
  omega.
intuition; subst; auto.
Save.

(* Why obligation from file "inductive.mlw", line 17, characters 5-14: *)
(*Why goal*) Lemma fib_po_2 : 
  forall (n: Z),
  forall (HW_1: n >= 0),
  forall (HW_3: 0 > n \/ 0 <= n /\ n > 1),
  (Zwf 0 (n - 1) n).
Proof.
intuition.
Save.

(* Why obligation from file "inductive.mlw", line 17, characters 5-14: *)
(*Why goal*) Lemma fib_po_3 : 
  forall (n: Z),
  forall (HW_1: n >= 0),
  forall (HW_3: 0 > n \/ 0 <= n /\ n > 1),
  forall (HW_4: (Zwf 0 (n - 1) n)),
  (n - 1) >= 0.
Proof.
intuition.
Save.

(* Why obligation from file "inductive.mlw", line 17, characters 19-28: *)
(*Why goal*) Lemma fib_po_4 : 
  forall (n: Z),
  forall (HW_1: n >= 0),
  forall (HW_3: 0 > n \/ 0 <= n /\ n > 1),
  forall (HW_4: (Zwf 0 (n - 1) n)),
  forall (HW_5: (n - 1) >= 0),
  forall (result: Z),
  forall (HW_6: (isfib (n - 1) result)),
  (Zwf 0 (n - 2) n).
Proof.
intuition.
Save.

(* Why obligation from file "inductive.mlw", line 17, characters 19-28: *)
(*Why goal*) Lemma fib_po_5 : 
  forall (n: Z),
  forall (HW_1: n >= 0),
  forall (HW_3: 0 > n \/ 0 <= n /\ n > 1),
  forall (HW_4: (Zwf 0 (n - 1) n)),
  forall (HW_5: (n - 1) >= 0),
  forall (result: Z),
  forall (HW_6: (isfib (n - 1) result)),
  forall (HW_7: (Zwf 0 (n - 2) n)),
  (n - 2) >= 0.
Proof.
intuition.
Save.

(* Why obligation from file "inductive.mlw", line 18, characters 4-19: *)
(*Why goal*) Lemma fib_po_6 : 
  forall (n: Z),
  forall (HW_1: n >= 0),
  forall (HW_3: 0 > n \/ 0 <= n /\ n > 1),
  forall (HW_4: (Zwf 0 (n - 1) n)),
  forall (HW_5: (n - 1) >= 0),
  forall (result: Z),
  forall (HW_6: (isfib (n - 1) result)),
  forall (HW_7: (Zwf 0 (n - 2) n)),
  forall (HW_8: (n - 2) >= 0),
  forall (result0: Z),
  forall (HW_9: (isfib (n - 2) result0)),
  (isfib n (result + result0)).
Proof.
intros.
replace n with ((n-2)+2) by omega.
replace (result+result0) with (result0+result) by omega.
apply isfibn.
split; auto.
split; auto.
replace (n-2+1) with (n-1) by omega.
apply HW_6.
Save.

