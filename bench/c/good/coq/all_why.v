(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.


Proof.
intuition.Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
Qed.


Proof.
intuition.
Qed.


Proof.
intuition.
Qed.


Proof.
intuition.
Qed.


Proof.
intuition.
Qed.


Proof.
intuition.
Qed.


Proof.
intuition.
Qed.


Proof.
intuition.
Qed.


Proof.
tauto.
Qed.

Proof.
intuition.
subst c_aux_2 x; auto.
Qed.


Proof.
intuition.
replace x0 with 1%Z; omega.
Qed.


Proof.
intuition.
Qed.

Proof.
intuition.
subst x c_aux_3 c_aux_4.
AccessSame.
Qed.

Proof.
intuition.
Qed.


Proof.
intuition.
Qed.


Proof.
intuition.
Qed.


Proof.
intuition.
Qed.


Proof.
intuition.
Qed.


Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/all.why", characters 34-83 *)
Lemma f1_impl_po_1 : 
  forall (x0: Z),
  forall (Post1: x0 = 0),
  x0 = 0.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/all.why", characters 121-197 *)
Lemma f2_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  x0 = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/all.why", characters 235-311 *)
Lemma f3_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  x0 = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/all.why", characters 453-461 *)
Lemma f4_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (caduceus: Z),
  forall (Post2: caduceus = x),
  forall (x0: Z),
  forall (Post1: x0 = (caduceus + 1)),
  x0 = 1 /\ caduceus = 0.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/all.why", characters 621-623 *)
Lemma f5_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  x0 = 1 /\ x0 = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/all.why", characters 706-782 *)
Lemma f6_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 1),
  forall (x0: Z),
  forall (Post1: x0 = (x + 2)),
  x0 = 3.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/all.why", characters 870-916 *)
Lemma f7a_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (caduceus_1: Z),
  forall (Post1: caduceus_1 = x),
  forall (result: bool),
  forall (Post5: (if result then caduceus_1 = 0 else caduceus_1 <> 0)),
  (if result then 1 = 1 else 2 = 1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/all.why", characters 1041-1087 *)
Lemma f7b_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x <> 0),
  forall (caduceus_1: Z),
  forall (Post1: caduceus_1 = x),
  forall (result: bool),
  forall (Post5: (if result then caduceus_1 = 0 else caduceus_1 <> 0)),
  (if result then 1 = 2 else 2 = 2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/all.why", characters 1272-1318 *)
Lemma t1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (Pre3: (valid_index alloc t 0) /\ (acc intP (shift t 0)) = 1),
  forall (caduceus_1: pointer),
  forall (Post1: caduceus_1 = t),
  forall (result: pointer),
  forall (Post4: result = (shift caduceus_1 0)),
  (forall (result0:Z), (result0 = (acc intP result) -> result0 = 1)) /\
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/all.why", characters 1759-1767 *)
Lemma t2_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (x: Z),
  forall (Pre3: ((valid_index alloc t 0) /\ x = 0) /\
                (acc intP (shift t 0)) = 1),
  forall (caduceus_1: pointer),
  forall (Post3: caduceus_1 = t),
  forall (caduceus: Z),
  forall (Post2: caduceus = x),
  forall (x0: Z),
  forall (Post1: x0 = (caduceus + 1)),
  (forall (result:pointer),
   (result = (shift caduceus_1 caduceus) ->
    (forall (result0:Z), (result0 = (acc intP result) -> result0 = 1)) /\
    (valid alloc result))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/all.why", characters 2144-2146 *)
Lemma t3_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (x: Z),
  forall (Pre3: ((valid_index alloc t 1) /\ x = 0) /\
                (acc intP (shift t 1)) = 1),
  forall (caduceus_1: pointer),
  forall (Post2: caduceus_1 = t),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  (forall (result:pointer),
   (result = (shift caduceus_1 x0) ->
    (forall (result0:Z), (result0 = (acc intP result) -> result0 = 1)) /\
    (valid alloc result))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/all.why", characters 2385-2432 *)
Lemma t4_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (x: Z),
  forall (Pre6: ((valid_index alloc t 2) /\ x = 2) /\
                (acc intP (shift t 2)) = 3),
  forall (caduceus_1: pointer),
  forall (Post1: caduceus_1 = t),
  forall (result: pointer),
  forall (Post5: result = (shift caduceus_1 x)),
  (forall (result0:Z),
   (result0 = (acc intP result) ->
    (forall (result1:Z),
     (result1 = x ->
      (forall (x:Z),
       (x = (result1 + 1) ->
        (forall (intP0:((memory) Z)),
         (intP0 = (upd intP result (result0 + result1)) -> x = 3 /\
          (acc intP0 (shift t 2)) = 5)) /\
        (valid alloc result))))))) /\
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

