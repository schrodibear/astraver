(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/invariants.why", characters 337-394 *)
Lemma f_impl_po_1 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: (n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (0 <= (acc x s) /\
                (acc x s) <= (acc y s)) /\ (acc y s) <= 100) /\
                (constant_c intP c alloc) /\ (valid_s s alloc) /\
                (valid_c c alloc)),
  (valid alloc s).
Proof.
intuition.
Save.

(* Why obligation from file "why/invariants.why", characters 540-582 *)
Lemma f_impl_po_2 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: (n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (0 <= (acc x s) /\
                (acc x s) <= (acc y s)) /\ (acc y s) <= 100) /\
                (constant_c intP c alloc) /\ (valid_s s alloc) /\
                (valid_c c alloc)),
  forall (Pre6: (valid alloc s)),
  forall (t: Z),
  forall (Post7: t = ((acc x s) + n)),
  forall (Pre5: (valid alloc s)),
  forall (Test2: t <= ((acc y s) - 20)),
  forall (caduceus_2: pointer),
  forall (Post5: caduceus_2 = s),
  (valid alloc (shift c 0)).
Proof.
unfold valid_s ;
unfold valid_c ;
intuition.
Save.

(* Why obligation from file "why/invariants.why", characters 517-583 *)
Lemma f_impl_po_3 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: (n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (0 <= (acc x s) /\
                (acc x s) <= (acc y s)) /\ (acc y s) <= 100) /\
                (constant_c intP c alloc) /\ (valid_s s alloc) /\
                (valid_c c alloc)),
  forall (Pre6: (valid alloc s)),
  forall (t: Z),
  forall (Post7: t = ((acc x s) + n)),
  forall (Pre5: (valid alloc s)),
  forall (Test2: t <= ((acc y s) - 20)),
  forall (caduceus_2: pointer),
  forall (Post5: caduceus_2 = s),
  forall (Pre4: (valid alloc (shift c 0))),
  forall (aux_4: Z),
  forall (Post4: aux_4 = (t + (acc intP (shift c 0)))),
  (valid alloc caduceus_2).
Proof.
intuition.
subst; auto.
Save.

(* Why obligation from file "why/invariants.why", characters 517-583 *)
Lemma f_impl_po_4 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: (n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (0 <= (acc x s) /\
                (acc x s) <= (acc y s)) /\ (acc y s) <= 100) /\
                (constant_c intP c alloc) /\ (valid_s s alloc) /\
                (valid_c c alloc)),
  forall (Pre6: (valid alloc s)),
  forall (t: Z),
  forall (Post7: t = ((acc x s) + n)),
  forall (Pre5: (valid alloc s)),
  forall (Test2: t <= ((acc y s) - 20)),
  forall (caduceus_2: pointer),
  forall (Post5: caduceus_2 = s),
  forall (Pre4: (valid alloc (shift c 0))),
  forall (aux_4: Z),
  forall (Post4: aux_4 = (t + (acc intP (shift c 0)))),
  forall (Pre1: (valid alloc caduceus_2)),
  forall (x0: ((memory) Z)),
  forall (Post13: x0 = (upd x caduceus_2 aux_4)),
  (0 <= (acc x0 s) /\ (acc x0 s) <= (acc y s)) /\ (acc y s) <= 100.
Proof.
intuition.
subst; caduceus.
subst; caduceus.
Save.

(* Why obligation from file "why/invariants.why", characters 593-593 *)
Lemma f_impl_po_5 : 
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre7: (n >= 0 /\ (acc intP (shift c 0)) = 12 /\ (0 <= (acc x s) /\
                (acc x s) <= (acc y s)) /\ (acc y s) <= 100) /\
                (constant_c intP c alloc) /\ (valid_s s alloc) /\
                (valid_c c alloc)),
  forall (Pre6: (valid alloc s)),
  forall (t: Z),
  forall (Post7: t = ((acc x s) + n)),
  forall (Pre5: (valid alloc s)),
  forall (Test1: t > ((acc y s) - 20)),
  forall (result0: unit),
  forall (Post1: result0 = tt),
  (0 <= (acc x s) /\ (acc x s) <= (acc y s)) /\ (acc y s) <= 100.
Proof.
intuition.
Save.

(* Why obligation from file "why/invariants.why", characters 899-923 *)
Lemma invariants_initially_established_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (Pre13: (constant_c intP c alloc) /\ (valid_s s alloc) /\
                 (valid_c c alloc)),
  forall (caduceus_4: pointer),
  forall (Post3: caduceus_4 = s),
  (valid alloc caduceus_4).
Proof.
intros;subst.
inversion_clear Pre13.
inversion_clear H0.
inversion_clear H2.
unfold valid_s in H0.
auto.
Save.

(* Why obligation from file "why/invariants.why", characters 876-923 *)
Lemma invariants_initially_established_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (c: pointer),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre13: (constant_c intP c alloc) /\ (valid_s s alloc) /\
                 (valid_c c alloc)),
  forall (caduceus_4: pointer),
  forall (Post3: caduceus_4 = s),
  forall (Pre3: (valid alloc caduceus_4)),
  forall (x0: ((memory) Z)),
  forall (Post13: x0 = (upd x caduceus_4 0)),
  (forall (result:pointer),
   (result = s ->
    (forall (y0:((memory) Z)),
     (y0 = (upd y result 0) ->
      (forall (result:pointer),
       (result = (shift c 0) ->
        (forall (intP0:((memory) Z)),
         (intP0 = (upd intP result 12) ->
          (forall (result:pointer),
           (result = (shift c 1) ->
            (forall (intP:((memory) Z)),
             (intP = (upd intP0 result 14) -> ((0 <= (acc x0 s) /\
              (acc x0 s) <= (acc y0 s)) /\ (acc y0 s) <= 100) /\
              (acc intP (shift c 0)) = 12)) /\
            (valid alloc result))))) /\
        (valid alloc result))))) /\
    (valid alloc result))).
Proof.
intuition;subst;auto;caduceus;
apply valid_range_valid_shift with 0 1;auto;
omega.
Qed.

