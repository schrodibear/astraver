(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_why.
Require Export LinkedLists.

(* Why obligation from file "why/reverse.why", characters 165-219 *)
Lemma rev_impl_po_1 : 
  forall (p0: pointer),
  forall (alloc: alloc),
  forall (tl: ((memory) pointer)),
  forall (Pre9: (is_list tl p0)),
  forall (p: pointer),
  forall (Post6: p = p0),
  forall (r: pointer),
  forall (Post5: r = p),
  forall (p2: pointer),
  forall (Post1: p2 = null),
  forall (Variant1: pointer),
  forall (p3: pointer),
  forall (r1: pointer),
  forall (tl0: ((memory) pointer)),
  forall (Pre8: Variant1 = r1),
  forall (Pre7: (exists lp:plist,
                 (exists lr:plist, (((llist tl0 p3 lp) /\
                  (llist tl0 r1 lr)) /\ (disjoint lp lr)) /\
                  (forall (l:plist),
                   ((llist tl p0 l) -> (eq_list (app (rev lr) lp) (rev l))))))),
  forall (Test2: true = true),
  forall (caduceus_1: pointer),
  forall (Post2: caduceus_1 = r1),
  forall (result1: bool),
  forall (Post18: (if result1 then ~(caduceus_1 = null)
                   else caduceus_1 = null)),
  (if result1
   then (forall (result:pointer),
         (result = r1 ->
          (forall (r:pointer),
           (r = (acc tl0 r) ->
            (forall (tl1:((memory) pointer)),
             (tl1 = (upd tl0 result p3) ->
              (forall (p:pointer),
               (p = result ->
                (exists lp:plist,
                 (exists lr:plist, (((llist tl1 p lp) /\ (llist tl1 r lr)) /\
                  (disjoint lp lr)) /\
                  (forall (l:plist),
                   ((llist tl p0 l) -> (eq_list (app (rev lr) lp) (rev l)))))) /\
                (Zwf 0 r r1))))) /\
            (valid alloc result))) /\
          (valid alloc r1)))
   else (exists l0:plist, (llist tl0 p3 l0) /\ (llist tl p0 (rev l0)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/reverse.why", characters 536-555 *)
Lemma rev_impl_po_2 : 
  forall (p0: pointer),
  forall (alloc: alloc),
  forall (tl: ((memory) pointer)),
  forall (Pre9: (is_list tl p0)),
  forall (p: pointer),
  forall (Post6: p = p0),
  forall (r: pointer),
  forall (Post5: r = p),
  forall (p2: pointer),
  forall (Post1: p2 = null),
  forall (Variant1: pointer),
  forall (p3: pointer),
  forall (r1: pointer),
  forall (tl0: ((memory) pointer)),
  forall (Pre8: Variant1 = r1),
  forall (Pre7: (exists lp:plist,
                 (exists lr:plist, (((llist tl0 p3 lp) /\
                  (llist tl0 r1 lr)) /\ (disjoint lp lr)) /\
                  (forall (l:plist),
                   ((llist tl p0 l) -> (eq_list (app (rev lr) lp) (rev l))))))),
  forall (Test2: true = true),
  forall (q: pointer),
  forall (Post4: q = r1),
  forall (Pre6: (valid alloc r1)),
  forall (result2: pointer),
  forall (Post22: result2 = (acc tl0 r1)),
  result2 = (acc tl0 result2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/reverse.why", characters 249-482 *)
Lemma rev_impl_po_3 : 
  forall (p0: pointer),
  forall (tl: ((memory) pointer)),
  forall (Pre9: (is_list tl p0)),
  forall (p: pointer),
  forall (Post6: p = p0),
  forall (r: pointer),
  forall (Post5: r = p),
  forall (p2: pointer),
  forall (Post1: p2 = null),
  (exists lp:plist,
   (exists lr:plist, (((llist tl p2 lp) /\ (llist tl r lr)) /\
    (disjoint lp lr)) /\
    (forall (l:plist),
     ((llist tl p0 l) -> (eq_list (app (rev lr) lp) (rev l)))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

