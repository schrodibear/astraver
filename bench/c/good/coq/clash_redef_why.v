(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.


(* Why obligation from file "why/clash_redef.why", characters 56-416 *)
Lemma f3_impl_po_1 : 
  forall (p1: pointer),
  forall (p2_0: pointer),
  forall (alloc: alloc_table),
  forall (p2: ((memory) pointer)),
  forall (Pre4: (valid alloc p1) /\
                (forall (anonymous_0:pointer),
                 ((valid alloc anonymous_0) ->
                  (valid_anonymous_0_p2 (acc p2 anonymous_0))))),
  forall (Pre3: (valid alloc p1)),
  forall (p2_1: ((memory) pointer)),
  forall (Post4: p2_1 = (upd p2 p1 p2_0)),
  forall (result0: Z),
  forall (Post3: result0 = 0),
  result0 = 0 /\
  (forall (anonymous_0:pointer),
   ((valid alloc anonymous_0) ->
    (valid_anonymous_0_p2 (acc p2_1 anonymous_0)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

