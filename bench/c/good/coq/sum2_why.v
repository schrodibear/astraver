
Require Import caduceus_why.


Admitted.

Admitted.

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

Proof.
Admitted.



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

(* Why obligation from file "why/sum2.why", characters 185-231 *)
Lemma test1_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (Post5: i = (any_int tt)),
  forall (s: Z),
  forall (Post4: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (s1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ s1 = (sum intP t 0 i2)),
  forall (Test2: true = true),
  forall (caduceus_1: Z),
  forall (Post2: caduceus_1 = i2),
  forall (result1: bool),
  forall (Post16: (if result1 then caduceus_1 < n else caduceus_1 >= n)),
  (if result1
   then (forall (result:pointer),
         (result = (shift t i2) ->
          (forall (result0:Z),
           (result0 = (acc intP result) ->
            (forall (i:Z),
             (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\ (s1 + result0) =
              (sum intP t 0 i)) /\ (Zwf 0 (n - i) (n - i2)))))) /\
          (valid alloc result)))
   else s1 = (sum intP t 0 n)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 257-324 *)
Lemma test1_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (Post5: i = (any_int tt)),
  forall (s: Z),
  forall (Post4: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ s = (sum intP t 0 i1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 691-737 *)
Lemma test2_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (Post4: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre9: Variant1 = (n - i2)),
  forall (Pre8: (0 <= i2 /\ i2 <= n) /\ (sum intP0 t 0 n) =
                ((sum intP t 0 n) + i2)),
  forall (Test2: true = true),
  forall (caduceus_1: Z),
  forall (Post2: caduceus_1 = i2),
  forall (result1: bool),
  forall (Post17: (if result1 then caduceus_1 < n else caduceus_1 >= n)),
  (if result1
   then (forall (result:pointer),
         (result = (shift t i2) ->
          (forall (result0:Z),
           (result0 = (acc intP0 result) ->
            (forall (intP1:((memory) Z)),
             (intP1 = (upd intP0 result (result0 + 1)) ->
              (forall (i:Z),
               (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\ (sum intP1 t 0 n) =
                ((sum intP t 0 n) + i)) /\ (Zwf 0 (n - i) (n - i2)))))) /\
            (valid alloc result))) /\
          (valid alloc result)))
   else (sum intP0 t 0 n) = ((sum intP t 0 n) + n) /\
   (assigns alloc intP intP0 (all_loc t))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 765-871 *)
Lemma test2_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (Post4: i = (any_int tt)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ (sum intP t 0 n) = ((sum intP t 0 n) + i1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

