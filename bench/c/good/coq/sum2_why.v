
Require Import caduceus_why.


(*Why logic*) Definition sum : ((memory) Z) -> pointer -> Z -> Z -> Z.
Admitted.

(*Why axiom*) Lemma sum1 :
  (forall (intP:((memory) Z)),
   (forall (t:pointer), (forall (i:Z), (sum intP t i i) = 0))).
Admitted.

(* Why obligation from file "sum2.why", characters 334-378 *)
Lemma test1_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range t 0 n)),
  forall (i: Z),
  forall (Post7: i = (any_int tt)),
  forall (s: Z),
  forall (Post6: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (s1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ s1 = (sum intP t 0 i2)),
  forall (Test2: true = true),
  forall (caduceus1: Z),
  forall (Post2: caduceus1 = i2),
  forall (result1: bool),
  forall (Post19: (if result1 then caduceus1 < n else caduceus1 >= n)),
  (if result1
   then (if 1
         then (forall (result:pointer),
               (result = (shift t i2) ->
                (forall (result0:Z),
                 (result0 = (acc intP result) ->
                  (forall (i:Z),
                   (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\ (s1 + result0) =
                    (sum intP t 0 i)) /\ (Zwf 0 (n - i) (n - i2)))))) /\
                ~(result = null) /\ 0 <= (offset result) /\ (offset result) <
                (block_length result)))
         else s1 = (sum intP t 0 n))
   else (if 0
         then (forall (result:pointer),
               (result = (shift t i2) ->
                (forall (result0:Z),
                 (result0 = (acc intP result) ->
                  (forall (i:Z),
                   (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\ (s1 + result0) =
                    (sum intP t 0 i)) /\ (Zwf 0 (n - i) (n - i2)))))) /\
                ~(result = null) /\ 0 <= (offset result) /\ (offset result) <
                (block_length result)))
         else s1 = (sum intP t 0 n))).
Proof.
intuition.
apply shift_not_null with (p:=t) (i:=i2).
apply valid_not_null with (i:=0) (j:=n).
auto.
subst; auto.
subst aux_1.
rewrite offset_shift.
assert (0 <= offset t + 0).
apply valid1 with (p:=t) (i:=0) (j:=n). 
assumption.
omega.
subst aux_1.
rewrite offset_shift.
rewrite length_shift.
assert (offset t + n <= length t).
apply valid3 with (i:=0).
assumption.
omega.
Qed.

(* Why obligation from file "sum2.why", characters 411-473 *)
Lemma test1_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range t 0 n)),
  forall (i: Z),
  forall (Post7: i = (any_int tt)),
  forall (s: Z),
  forall (Post6: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ s = (sum intP t 0 i1).
Proof.
intuition; subst; auto with *.
(* rewrite sum2... *)
Admitted.

Proof.
intuition.
assert (0<=n).
apply valid2 with t; auto.
omega.
subst.
(* rewrite sum1... *)
Admitted.

Proof.
intuition.
assert (i2=n).
omega.
subst; auto.
Save.

(* Why obligation from file "sum2.why", characters 826-870 *)
Lemma test2_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_range t 0 n)),
  forall (i: Z),
  forall (Post6: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre9: Variant1 = (n - i2)),
  forall (Pre8: (0 <= i2 /\ i2 <= n) /\ (sum intP0 t 0 n) =
                ((sum intP t 0 n) + i2)),
  forall (Test2: true = true),
  forall (caduceus2: Z),
  forall (Post2: caduceus2 = i2),
  forall (result1: bool),
  forall (Post20: (if result1 then caduceus2 < n else caduceus2 >= n)),
  (if result1
   then (if 1
         then (forall (result:pointer),
               (result = (shift t i2) ->
                (forall (result0:Z),
                 (result0 = (acc intP0 result) ->
                  (forall (intP1:((memory) Z)),
                   (intP1 = (upd intP0 result (result0 + 1)) ->
                    (forall (i:Z),
                     (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\
                      (sum intP1 t 0 n) = ((sum intP t 0 n) + i)) /\
                      (Zwf 0 (n - i) (n - i2)))))) /\
                  ~(result = null) /\ 0 <= (offset result) /\
                  (offset result) < (block_length result))) /\
                ~(result = null) /\ 0 <= (offset result) /\ (offset result) <
                (block_length result)))
         else (sum intP0 t 0 n) = ((sum intP t 0 n) + n))
   else (if 0
         then (forall (result:pointer),
               (result = (shift t i2) ->
                (forall (result0:Z),
                 (result0 = (acc intP0 result) ->
                  (forall (intP1:((memory) Z)),
                   (intP1 = (upd intP0 result (result0 + 1)) ->
                    (forall (i:Z),
                     (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\
                      (sum intP1 t 0 n) = ((sum intP t 0 n) + i)) /\
                      (Zwf 0 (n - i) (n - i2)))))) /\
                  ~(result = null) /\ 0 <= (offset result) /\
                  (offset result) < (block_length result))) /\
                ~(result = null) /\ 0 <= (offset result) /\ (offset result) <
                (block_length result)))
         else (sum intP0 t 0 n) = ((sum intP t 0 n) + n))).
Proof.
Admitted.



(* Why obligation from file "sum2.why", characters 912-1013 *)
Lemma test2_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_range t 0 n)),
  forall (i: Z),
  forall (Post6: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ (sum intP t 0 n) = ((sum intP t 0 n) + i1).
Proof.
intuition; subst; auto with *.
(* TODO *)
Save.


Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

