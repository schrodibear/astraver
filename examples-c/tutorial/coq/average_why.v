(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/average.why", characters 426-455 *)
Lemma average_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre7: (valid_range alloc t 0 n) /\ n > 0),
  forall (sum: Z),
  forall (Post3: sum = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (sum1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ (i2 * (min intP t i2)) <= sum1),
  forall (Test2: i2 < n),
  forall (aux_1: pointer),
  forall (Post13: aux_1 = (shift t i2)),
  (valid alloc aux_1).
Proof.
intuition.
subst; auto.
Save.

(* Why obligation from file "why/average.why", characters 426-455 *)
Lemma average_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre7: (valid_range alloc t 0 n) /\ n > 0),
  forall (sum: Z),
  forall (Post3: sum = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (sum1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ (i2 * (min intP t i2)) <= sum1),
  forall (Test2: i2 < n),
  forall (aux_1: pointer),
  forall (Post13: aux_1 = (shift t i2)),
  forall (Pre2: (valid alloc aux_1)),
  forall (result1: Z),
  forall (Post15: result1 = (acc intP aux_1)),
  (forall (i:Z),
   (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\ (i * (min intP t i)) <=
    (sum1 + result1)) /\ (Zwf 0 (n - i) (n - i2)))).
Proof.
intuition.
subst.
assert (i2=0 \/ i2>0). omega. intuition.
subst; ring (0+1).
assert (min intP t 1 = shift t 0 # intP).
generalize (min_is_min alloc intP t 1).
assert (1>0). omega. unfold is_min in *|-*. intuition.
elim H7; intros i Hi. assert (i=0). omega.
subst; intuition.
omega.
replace ((i2 + 1) * min intP t (i2 + 1)) with ((i2 * min intP t (i2+1)) + min intP t (i2+1)).
2:ring.
assert (min intP t (i2 + 1) <= min intP t i2).
generalize (min_is_min alloc intP t i2).
assert (i2+1>0). omega.
generalize (min_is_min alloc intP t (i2+1)).
unfold is_min; intuition.
elim H9; intros i Hi.
intuition.
rewrite H11.
intuition.
assert (i2 * min intP t (i2 + 1) <= i2 * min intP t i2).
apply Zmult_le_compat_l; auto with *.
assert (min intP t (i2 + 1) <= shift t i2 # intP).
assert (i2+1>0). omega.
generalize (min_is_min alloc intP t (i2+1)).
unfold is_min; intuition.
omega.
Qed.

(* Why obligation from file "why/average.why", characters 232-493 *)
Lemma average_impl_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre7: (valid_range alloc t 0 n) /\ n > 0),
  forall (sum: Z),
  forall (Post3: sum = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (sum1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ (i2 * (min intP t i2)) <= sum1),
  forall (Test1: i2 >= n),
  (min intP t n) <= ((Zdiv sum1 n)) /\ ~(n = 0).
Proof.
intuition.
assert (i2 = n). omega. subst.
replace (min intP t n) with ((0 + min intP t n * n) / n).
apply Zge_le.
apply Z_div_ge; auto.
rewrite Zmult_comm.
omega.
rewrite Z_div_plus; auto.
Save.

(* Why obligation from file "why/average.why", characters 281-367 *)
Lemma average_impl_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre7: (valid_range alloc t 0 n) /\ n > 0),
  forall (sum: Z),
  forall (Post3: sum = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ (i1 * (min intP t i1)) <= sum.
Proof.
intuition.
subst; omega.
Qed.

(* Why obligation from file "why/average.why", characters 742-770 *)
Lemma min_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (Pre10: n > 0 /\ (valid_range alloc t 0 n)),
  forall (aux_1: pointer),
  forall (Post10: aux_1 = (shift t 0)),
  (valid alloc aux_1).
Proof.
intuition.
subst; auto.
Save.

(* Why obligation from file "why/average.why", characters 742-770 *)
Lemma min_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre10: n > 0 /\ (valid_range alloc t 0 n)),
  forall (aux_1: pointer),
  forall (Post10: aux_1 = (shift t 0)),
  forall (Pre1: (valid alloc aux_1)),
  forall (result: Z),
  forall (Post12: result = (acc intP aux_1)),
  (forall (i:Z),
   (i = 1 -> ((1 <= i /\ i <= n) /\ (is_min alloc intP t i result)) /\
    (forall (i:Z),
     (forall (tmp:Z),
      ((1 <= i /\ i <= n) /\ (is_min alloc intP t i tmp) ->
       ((i < n ->
         (forall (result:pointer),
          (result = (shift t i) ->
           (forall (result0:Z),
            (result0 = (acc intP result) ->
             ((result0 < tmp ->
               (forall (result:pointer),
                (result = (shift t i) ->
                 (forall (result0:Z),
                  (result0 = (acc intP result) ->
                   (forall (i0:Z),
                    (i0 = (i + 1) -> ((1 <= i0 /\ i0 <= n) /\
                     (is_min alloc intP t i0 result0)) /\
                     (Zwf 0 (n - i0) (n - i)))))) /\
                 (valid alloc result))))) /\
             ((result0 >= tmp ->
               (forall (i0:Z),
                (i0 = (i + 1) -> ((1 <= i0 /\ i0 <= n) /\
                 (is_min alloc intP t i0 tmp)) /\ (Zwf 0 (n - i0) (n - i)))))))) /\
           (valid alloc result))))) /\
       ((i >= n -> (is_min alloc intP t n tmp)))))))).
Proof.
unfold is_min; intuition; subst; auto with *.
assert (i1=0). omega.
subst; intuition.
exists 0; intuition.
assert (i3<i1 \/ i3=i1). omega. intuition.
generalize (H3 i3); intuition.
subst; omega.
exists i1; intuition.
assert (i3<i1 \/ i3=i1). omega. intuition.
subst; omega.
elim H6; intros i2 Hi2; exists i2; intuition.
assert (i1=n). omega. subst; trivial.
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

