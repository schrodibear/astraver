(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Export Match.

(*Why*) Parameter OUTPUT : (j: Z)unit.

(*Why*) Parameter memcmp :
  (i: Z)(j: Z)(n: Z)(x: (array Z))(y: (array Z))
  (sig_1 Z [result: Z](((`result = 0` -> (match x i y j n))) /\
   ((`result <> 0` -> ~(match x i y j n))))).

(* Why obligation from file "not_so_naive.c", characters 520-524 *)
Lemma NSN_po_1 : 
  (m: Z)
  (n: Z)
  (x: (array Z))
  (y: (array Z))
  (Pre12: `(array_length x) = m` /\ `(array_length y) = n` /\ `0 <= n` /\
          `2 <= m`)
  `0 <= 0` /\ `0 < (array_length x)`.
Proof.
Auto with *.
Save.

(* Why obligation from file "not_so_naive.c", characters 528-532 *)
Lemma NSN_po_2 : 
  (m: Z)
  (n: Z)
  (x: (array Z))
  (y: (array Z))
  (Pre12: `(array_length x) = m` /\ `(array_length y) = n` /\ `0 <= n` /\
          `2 <= m`)
  (Pre2: `0 <= 0` /\ `0 < (array_length x)`)
  (c_aux_1: Z)
  (Post2: c_aux_1 = (access x `0`))
  `0 <= 1` /\ `1 < (array_length x)`.
Proof.
Auto with *.
Save.

(* Why obligation from file "not_so_naive.c", characters 520-532 *)
Lemma NSN_po_3 : 
  (m: Z)
  (n: Z)
  (x: (array Z))
  (y: (array Z))
  (Pre12: `(array_length x) = m` /\ `(array_length y) = n` /\ `0 <= n` /\
          `2 <= m`)
  (Pre2: `0 <= 0` /\ `0 < (array_length x)`)
  (c_aux_1: Z)
  (Post2: c_aux_1 = (access x `0`))
  (Pre1: `0 <= 1` /\ `1 < (array_length x)`)
  (c_aux_2: Z)
  (Post1: c_aux_2 = (access x `1`))
  (result: bool)
  (Post27: (if result then `c_aux_1 = c_aux_2` else `c_aux_1 <> c_aux_2`))
  (if result
   then ((k:Z)
         (k = `2` ->
          ((ell:Z)
           (ell = `1` -> ((j:Z) (j = `0` -> `0 <= j`)) /\ `k > 0` /\
            `ell > 0`))))
   else ((k:Z)
         (k = `1` ->
          ((ell:Z)
           (ell = `2` -> ((j:Z) (j = `0` -> `0 <= j`)) /\ `k > 0` /\
            `ell > 0`))))).
Proof.
Destruct result; Intuition.
Save.

(* Why obligation from file "not_so_naive.c", characters 757-761 *)
Lemma NSN_po_4 : 
  (m: Z)
  (n: Z)
  (x: (array Z))
  (y: (array Z))
  (Pre12: `(array_length x) = m` /\ `(array_length y) = n` /\ `0 <= n` /\
          `2 <= m`)
  (ell1: Z)
  (k1: Z)
  (Pre11: `k1 > 0` /\ `ell1 > 0`)
  (j1: Z)
  (Post7: j1 = `0`)
  (Variant1: Z)
  (j2: Z)
  (Pre10: Variant1 = `n - m - j2`)
  (Pre9: `0 <= j2`)
  (Test2: `j2 <= n - m`)
  `0 <= 1` /\ `1 < (array_length x)`.
Proof.
Auto with *.
Save.

(* Why obligation from file "not_so_naive.c", characters 765-773 *)
Lemma NSN_po_5 : 
  (m: Z)
  (n: Z)
  (x: (array Z))
  (y: (array Z))
  (Pre12: `(array_length x) = m` /\ `(array_length y) = n` /\ `0 <= n` /\
          `2 <= m`)
  (ell1: Z)
  (k1: Z)
  (Pre11: `k1 > 0` /\ `ell1 > 0`)
  (j1: Z)
  (Post7: j1 = `0`)
  (Variant1: Z)
  (j2: Z)
  (Pre10: Variant1 = `n - m - j2`)
  (Pre9: `0 <= j2`)
  (Test2: `j2 <= n - m`)
  (Pre5: `0 <= 1` /\ `1 < (array_length x)`)
  (c_aux_7: Z)
  (Post9: c_aux_7 = (access x `1`))
  `0 <= j2 + 1` /\ `j2 + 1 < (array_length y)`.
Proof.
Intuition.
Save.

(* Why obligation from file "not_so_naive.c", characters 757-773 *)
Lemma NSN_po_6 : 
  (m: Z)
  (n: Z)
  (x: (array Z))
  (y: (array Z))
  (Pre12: `(array_length x) = m` /\ `(array_length y) = n` /\ `0 <= n` /\
          `2 <= m`)
  (ell1: Z)
  (k1: Z)
  (Pre11: `k1 > 0` /\ `ell1 > 0`)
  (j1: Z)
  (Post7: j1 = `0`)
  (Variant1: Z)
  (j2: Z)
  (Pre10: Variant1 = `n - m - j2`)
  (Pre9: `0 <= j2`)
  (Test2: `j2 <= n - m`)
  (Pre5: `0 <= 1` /\ `1 < (array_length x)`)
  (c_aux_7: Z)
  (Post9: c_aux_7 = (access x `1`))
  (Pre4: `0 <= j2 + 1` /\ `j2 + 1 < (array_length y)`)
  (c_aux_8: Z)
  (Post8: c_aux_8 = (access y `j2 + 1`))
  (result3: bool)
  (Post30: (if result3 then `c_aux_7 <> c_aux_8` else `c_aux_7 = c_aux_8`))
  (if result3
   then ((j:Z)
         (j = `j2 + k1` -> `0 <= j` /\ (Zwf `0` `n - m - j` `n - m - j2`)))
   else ((result:Z)
         (result = `j2 + 2` ->
          ((result0:Z)
           (((`result0 = 0` -> (match x `2` y result `m - 2`))) /\
            ((`result0 <> 0` -> ~(match x `2` y result `m - 2`))) ->
            ((`result0 = 0` ->
              ((result:Z)
               (result = (access x `0`) ->
                ((result0:Z)
                 (result0 = (access y j2) ->
                  ((`result = result0` ->
                    ((j:Z)
                     (j = `j2 + ell1` -> `0 <= j` /\
                      (Zwf `0` `n - m - j` `n - m - j2`))) /\
                    (match x `0` y j2 (array_length x)))) /\
                  ((`result <> result0` ->
                    ((j:Z)
                     (j = `j2 + ell1` -> `0 <= j` /\
                      (Zwf `0` `n - m - j` `n - m - j2`))))))) /\
                `0 <= j2` /\ `j2 < (array_length y)`)) /\
              `0 <= 0` /\ `0 < (array_length x)`)) /\
            ((`result0 <> 0` ->
              ((j:Z)
               (j = `j2 + ell1` -> `0 <= j` /\
                (Zwf `0` `n - m - j` `n - m - j2`)))))))))).
Proof.
Destruct result3; Unfold Zwf; Intuition.
Subst.
Apply match_left_extension; Try Omega.
Apply match_left_extension; Try Omega.
Assumption.
Replace `j2+1+1` with `j2+2`; Try Omega.
Replace `(array_length x)-1-1` with `m-2`; Try Omega.
Assumption.
Save.
