(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Export Match.

(*Why*) Parameter OUTPUT : forall (j: Z), unit.

(*Why*) Parameter memcmp :
  forall (i: Z), forall (j: Z), forall (n: Z), forall (x: (array Z)),
  forall (y: (array Z)),
  (sig_1 Z
   (fun (result: Z)  => (((result = 0 -> (match_ x i y j n))) /\
    ((result <> 0 -> ~(match_ x i y j n)))))).

(* Why obligation from file "not_so_naive.c", characters 523-527 *)
Lemma NSN_po_1 : 
  forall (m: Z),
  forall (n: Z),
  forall (x: (array Z)),
  forall (y: (array Z)),
  forall (Pre12: (array_length x) = m /\ (array_length y) = n /\ 0 <= n /\
                 2 <= m),
  0 <= 0 /\ 0 < (array_length x).
Proof.
auto with *.
Qed.

(* Why obligation from file "not_so_naive.c", characters 531-535 *)
Lemma NSN_po_2 : 
  forall (m: Z),
  forall (n: Z),
  forall (x: (array Z)),
  forall (y: (array Z)),
  forall (Pre12: (array_length x) = m /\ (array_length y) = n /\ 0 <= n /\
                 2 <= m),
  forall (Pre2: 0 <= 0 /\ 0 < (array_length x)),
  forall (c_aux_1: Z),
  forall (Post2: c_aux_1 = (access x 0)),
  0 <= 1 /\ 1 < (array_length x).
Proof.
auto with *.
Qed.

(* Why obligation from file "not_so_naive.c", characters 523-535 *)
Lemma NSN_po_3 : 
  forall (m: Z),
  forall (n: Z),
  forall (x: (array Z)),
  forall (y: (array Z)),
  forall (Pre12: (array_length x) = m /\ (array_length y) = n /\ 0 <= n /\
                 2 <= m),
  forall (Pre2: 0 <= 0 /\ 0 < (array_length x)),
  forall (c_aux_1: Z),
  forall (Post2: c_aux_1 = (access x 0)),
  forall (Pre1: 0 <= 1 /\ 1 < (array_length x)),
  forall (c_aux_2: Z),
  forall (Post1: c_aux_2 = (access x 1)),
  forall (result: bool),
  forall (Post27: (if result then c_aux_1 = c_aux_2 else c_aux_1 <> c_aux_2)),
  (if result
   then (forall (k:Z),
         (k = 2 ->
          (forall (ell:Z),
           (ell = 1 -> (forall (j:Z), (j = 0 -> 0 <= j)) /\ k > 0 /\ ell > 0))))
   else (forall (k:Z),
         (k = 1 ->
          (forall (ell:Z),
           (ell = 2 -> (forall (j:Z), (j = 0 -> 0 <= j)) /\ k > 0 /\ ell > 0))))).
Proof.
olddestruct result; intuition.
Qed.

(* Why obligation from file "not_so_naive.c", characters 760-764 *)
Lemma NSN_po_4 : 
  forall (m: Z),
  forall (n: Z),
  forall (x: (array Z)),
  forall (y: (array Z)),
  forall (Pre12: (array_length x) = m /\ (array_length y) = n /\ 0 <= n /\
                 2 <= m),
  forall (ell1: Z),
  forall (k1: Z),
  forall (Pre11: k1 > 0 /\ ell1 > 0),
  forall (j1: Z),
  forall (Post7: j1 = 0),
  forall (Variant1: Z),
  forall (j2: Z),
  forall (Pre10: Variant1 = (n - m - j2)),
  forall (Pre9: 0 <= j2),
  forall (Test2: j2 <= (n - m)),
  0 <= 1 /\ 1 < (array_length x).
Proof.
auto with *.
Qed.

(* Why obligation from file "not_so_naive.c", characters 768-776 *)
Lemma NSN_po_5 : 
  forall (m: Z),
  forall (n: Z),
  forall (x: (array Z)),
  forall (y: (array Z)),
  forall (Pre12: (array_length x) = m /\ (array_length y) = n /\ 0 <= n /\
                 2 <= m),
  forall (ell1: Z),
  forall (k1: Z),
  forall (Pre11: k1 > 0 /\ ell1 > 0),
  forall (j1: Z),
  forall (Post7: j1 = 0),
  forall (Variant1: Z),
  forall (j2: Z),
  forall (Pre10: Variant1 = (n - m - j2)),
  forall (Pre9: 0 <= j2),
  forall (Test2: j2 <= (n - m)),
  forall (Pre5: 0 <= 1 /\ 1 < (array_length x)),
  forall (c_aux_7: Z),
  forall (Post9: c_aux_7 = (access x 1)),
  0 <= (j2 + 1) /\ (j2 + 1) < (array_length y).
Proof.
intuition.
Qed.

(* Why obligation from file "not_so_naive.c", characters 760-776 *)
Lemma NSN_po_6 : 
  forall (m: Z),
  forall (n: Z),
  forall (x: (array Z)),
  forall (y: (array Z)),
  forall (Pre12: (array_length x) = m /\ (array_length y) = n /\ 0 <= n /\
                 2 <= m),
  forall (ell1: Z),
  forall (k1: Z),
  forall (Pre11: k1 > 0 /\ ell1 > 0),
  forall (j1: Z),
  forall (Post7: j1 = 0),
  forall (Variant1: Z),
  forall (j2: Z),
  forall (Pre10: Variant1 = (n - m - j2)),
  forall (Pre9: 0 <= j2),
  forall (Test2: j2 <= (n - m)),
  forall (Pre5: 0 <= 1 /\ 1 < (array_length x)),
  forall (c_aux_7: Z),
  forall (Post9: c_aux_7 = (access x 1)),
  forall (Pre4: 0 <= (j2 + 1) /\ (j2 + 1) < (array_length y)),
  forall (c_aux_8: Z),
  forall (Post8: c_aux_8 = (access y (j2 + 1))),
  forall (result3: bool),
  forall (Post30: (if result3 then c_aux_7 <> c_aux_8 else c_aux_7 = c_aux_8)),
  (if result3
   then (forall (j:Z),
         (j = (j2 + k1) -> 0 <= j /\ (Zwf 0 (n - m - j) (n - m - j2))))
   else (forall (result:Z),
         (result = (j2 + 2) ->
          (forall (result0:Z),
           (((result0 = 0 -> (match_ x 2 y result (m - 2)))) /\
            ((result0 <> 0 -> ~(match_ x 2 y result (m - 2)))) ->
            ((result0 = 0 ->
              (forall (result:Z),
               (result = (access x 0) ->
                (forall (result0:Z),
                 (result0 = (access y j2) ->
                  ((result = result0 ->
                    (forall (j:Z),
                     (j = (j2 + ell1) -> 0 <= j /\
                      (Zwf 0 (n - m - j) (n - m - j2)))) /\
                    (match_ x 0 y j2 (array_length x)))) /\
                  ((result <> result0 ->
                    (forall (j:Z),
                     (j = (j2 + ell1) -> 0 <= j /\
                      (Zwf 0 (n - m - j) (n - m - j2)))))))) /\
                0 <= j2 /\ j2 < (array_length y))) /\
              0 <= 0 /\ 0 < (array_length x))) /\
            ((result0 <> 0 ->
              (forall (j:Z),
               (j = (j2 + ell1) -> 0 <= j /\ (Zwf 0 (n - m - j) (n - m - j2))))))))))).
Proof.
olddestruct result3; unfold Zwf; intuition.
subst.
apply match_left_extension; try omega.
apply match_left_extension; try omega.
assumption.
replace (j2 + 1 + 1)%Z with (j2 + 2)%Z; try omega.
replace (array_length x - 1 - 1)%Z with (m - 2)%Z; try omega.
assumption.
Qed.

