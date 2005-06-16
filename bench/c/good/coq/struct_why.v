(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export struct_spec_why.

(* Why obligation from file "why/struct.why", characters 209-228 *)
Lemma f_impl_po_1 : 
  forall (t2: pointer),
  forall (alloc: alloc_table),
  forall (x: ((memory) Z)),
  forall (Pre9: (* File \"struct.c\", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x t2) = 0)),
  forall (caduceus1: pointer),
  forall (Post4: caduceus1 = t2),
  (valid alloc caduceus1).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "why/struct.why", characters 193-281 *)
Lemma f_impl_po_2 : 
  forall (t2: pointer),
  forall (alloc: alloc_table),
  forall (x: ((memory) Z)),
  forall (y: ((memory) Z)),
  forall (Pre9: (* File \"struct.c\", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x t2) = 0)),
  forall (caduceus1: pointer),
  forall (Post4: caduceus1 = t2),
  forall (Pre4: (valid alloc caduceus1)),
  forall (caduceus2: Z),
  forall (Post3: caduceus2 = (acc x caduceus1)),
  forall (Pre3: (valid alloc caduceus1)),
  forall (x0: ((memory) Z)),
  forall (Post10: x0 = (upd x caduceus1 (caduceus2 + 1))),
  (forall (result:pointer),
   (result = t2 ->
    (forall (result0:Z),
     (result0 = (acc x0 result) ->
      (forall (x1:((memory) Z)),
       (x1 = (upd x0 result (1 + result0)) ->
        (forall (result:Z),
         (result = result0 ->
          (* File \"struct.c\", line 9, characters 13-63 *) ((result = 1 /\
          (acc x1 t2) = 2) /\ (acc y t2) = (acc y t2)) /\
          (not_assigns alloc x x1 (pset_singleton t2)))))) /\
      (valid alloc result))) /\
    (valid alloc result))).
Proof.
intuition; subst; caduceus; auto.
Save.

(* Why obligation from file "why/struct.why", characters 933-945 *)
Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (ps: pointer),
  forall (s: pointer),
  forall (t: ((memory) pointer)),
  forall (Pre11: (* File \"struct.c\", line 19, characters 14-24 *)
                 (valid alloc ps) /\ (valid_range alloc s 0 0) /\
                 (valid1 t) /\ (separation2 t t)),
  forall (ps0: pointer),
  forall (Post1: ps0 = s),
  (valid alloc s).
Proof.
 intuition.
Save.

(* Why obligation from file "why/struct.why", characters 971-984 *)
Lemma g_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (ps: pointer),
  forall (s: pointer),
  forall (t: ((memory) pointer)),
  forall (Pre11: (* File \"struct.c\", line 19, characters 14-24 *)
                 (valid alloc ps) /\ (valid_range alloc s 0 0) /\
                 (valid1 t) /\ (separation2 t t)),
  forall (ps0: pointer),
  forall (Post1: ps0 = s),
  forall (p1: pointer),
  forall (Post2: p1 = (acc t s)),
  (valid alloc ps0).
Proof.
 intuition.
subst; auto.
Save.

(* Why obligation from file "why/struct.why", characters 989-1013 *)
Lemma g_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (ps: pointer),
  forall (s: pointer),
  forall (t: ((memory) pointer)),
  forall (Pre11: (* File \"struct.c\", line 19, characters 14-24 *)
                 (valid alloc ps) /\ (valid_range alloc s 0 0) /\
                 (valid1 t) /\ (separation2 t t)),
  forall (ps0: pointer),
  forall (Post1: ps0 = s),
  forall (p1: pointer),
  forall (Post2: p1 = (acc t s)),
  forall (Pre7: (valid alloc ps0)),
  forall (caduceus_1: pointer),
  forall (Post5: caduceus_1 = (acc t ps0)),
  (valid alloc caduceus_1).
Proof.
intuition.
subst;
auto.
Save.

(* Why obligation from file "why/struct.why", characters 954-1013 *)
Lemma g_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (ps: pointer),
  forall (s: pointer),
  forall (t: ((memory) pointer)),
  forall (x: ((memory) Z)),
  forall (Pre11: (* File \"struct.c\", line 19, characters 14-24 *)
                 (valid alloc ps) /\ (valid_range alloc s 0 0) /\
                 (valid1 t) /\ (separation2 t t)),
  forall (ps0: pointer),
  forall (Post1: ps0 = s),
  forall (p1: pointer),
  forall (Post2: p1 = (acc t s)),
  forall (Pre7: (valid alloc ps0)),
  forall (caduceus_1: pointer),
  forall (Post5: caduceus_1 = (acc t ps0)),
  forall (Pre6: (valid alloc caduceus_1)),
  forall (x0: ((memory) Z)),
  forall (Post13: x0 = (upd x caduceus_1 1)),
  (((forall (result:Z),
     (result = (acc x0 (acc t s)) ->
      (* File \"struct.c\", line 20, characters 13-25 *) result = 1)) /\
  (valid alloc s)) /\ (valid alloc (acc t s))) /\ (valid alloc (acc t s)).
Proof.
intuition; subst; auto.
caduceus.
Save.

