(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Export Match.

(*Why*) Parameter OUTPUT : (j: Z)unit.

(* Why obligation from file "brute_force.c", characters 368-372 *)
Lemma BF_po_1 : 
  (m: Z)
  (n: Z)
  (x: (array Z))
  (y: (array Z))
  (Pre10: `(array_length x) = m` /\ `(array_length y) = n` /\ `0 <= n` /\
          `0 <= m`)
  (j1: Z)
  (Post1: j1 = `0`)
  (Variant1: Z)
  (j2: Z)
  (Pre9: Variant1 = `n - m + 1 - j2`)
  (Pre8: `0 <= j2`)
  (Test8: `j2 <= n - m`)
  (i2: Z)
  (Post2: i2 = `0`)
  (Variant3: Z)
  (i3: Z)
  (Pre6: Variant3 = `m - i3`)
  (Pre5: (`0 <= i3` /\ `i3 <= m`) /\ (match x `0` y j2 i3))
  (Test5: true = true)
  (Test4: `i3 < m`)
  `0 <= i3` /\ `i3 < (array_length x)`.
Proof.
Auto with *.
Save.

(* Why obligation from file "brute_force.c", characters 376-384 *)
Lemma BF_po_2 : 
  (m: Z)
  (n: Z)
  (x: (array Z))
  (y: (array Z))
  (Pre10: `(array_length x) = m` /\ `(array_length y) = n` /\ `0 <= n` /\
          `0 <= m`)
  (j1: Z)
  (Post1: j1 = `0`)
  (Variant1: Z)
  (j2: Z)
  (Pre9: Variant1 = `n - m + 1 - j2`)
  (Pre8: `0 <= j2`)
  (Test8: `j2 <= n - m`)
  (i2: Z)
  (Post2: i2 = `0`)
  (Variant3: Z)
  (i3: Z)
  (Pre6: Variant3 = `m - i3`)
  (Pre5: (`0 <= i3` /\ `i3 <= m`) /\ (match x `0` y j2 i3))
  (Test5: true = true)
  (Test4: `i3 < m`)
  (Pre4: `0 <= i3` /\ `i3 < (array_length x)`)
  (c_aux_1: Z)
  (Post4: c_aux_1 = (access x i3))
  `0 <= i3 + j2` /\ `i3 + j2 < (array_length y)`.
Proof.
Auto with *.
Save.

(* Why obligation from file "brute_force.c", characters 368-384 *)
Lemma BF_po_3 : 
  (m: Z)
  (n: Z)
  (x: (array Z))
  (y: (array Z))
  (Pre10: `(array_length x) = m` /\ `(array_length y) = n` /\ `0 <= n` /\
          `0 <= m`)
  (j1: Z)
  (Post1: j1 = `0`)
  (Variant1: Z)
  (j2: Z)
  (Pre9: Variant1 = `n - m + 1 - j2`)
  (Pre8: `0 <= j2`)
  (Test8: `j2 <= n - m`)
  (i2: Z)
  (Post2: i2 = `0`)
  (Variant3: Z)
  (i3: Z)
  (Pre6: Variant3 = `m - i3`)
  (Pre5: (`0 <= i3` /\ `i3 <= m`) /\ (match x `0` y j2 i3))
  (Test5: true = true)
  (Test4: `i3 < m`)
  (Pre4: `0 <= i3` /\ `i3 < (array_length x)`)
  (c_aux_1: Z)
  (Post4: c_aux_1 = (access x i3))
  (Pre3: `0 <= i3 + j2` /\ `i3 + j2 < (array_length y)`)
  (c_aux_2: Z)
  (Post3: c_aux_2 = (access y `i3 + j2`))
  (result4: bool)
  (Post26: (if result4 then `c_aux_1 = c_aux_2` else `c_aux_1 <> c_aux_2`))
  (if result4
   then ((i:Z)
         (i = `i3 + 1` -> ((`0 <= i` /\ `i <= m`) /\ (match x `0` y j2 i)) /\
          (Zwf `0` `m - i` `m - i3`)))
   else ((`i3 >= m` ->
          ((result:Z)
           (result = j2 ->
            ((j:Z)
             (j = `j2 + 1` -> `0 <= j` /\
              (Zwf `0` `n - m + 1 - j` `n - m + 1 - j2`))) /\
            (match x `0` y j2 (array_length x)))))) /\
   ((`i3 < m` ->
     ((j:Z)
      (j = `j2 + 1` -> `0 <= j` /\ (Zwf `0` `n - m + 1 - j` `n - m + 1 - j2`)))))).
Proof.
Destruct result6; Intuition.
Subst i.
Apply match_right_extension; Auto with *.
Subst c_aux_1 c_aux_2; Ring `0+i2`; Ring `j1+i2`; Assumption.
Unfold Zwf; Omega.
Unfold Zwf; Omega.
Subst result.
Assert i2=(array_length x). Omega. Subst i2; Assumption.
Unfold Zwf; Omega.
Save.

(* Why obligation from file "brute_force.c", characters 359-384 *)
Lemma BF_po_4 : 
  (m: Z)
  (n: Z)
  (x: (array Z))
  (y: (array Z))
  (Pre10: `(array_length x) = m` /\ `(array_length y) = n` /\ `0 <= n` /\
          `0 <= m`)
  (j1: Z)
  (Post1: j1 = `0`)
  (Variant1: Z)
  (j2: Z)
  (Pre9: Variant1 = `n - m + 1 - j2`)
  (Pre8: `0 <= j2`)
  (Test8: `j2 <= n - m`)
  (i2: Z)
  (Post2: i2 = `0`)
  (Variant3: Z)
  (i3: Z)
  (Pre6: Variant3 = `m - i3`)
  (Pre5: (`0 <= i3` /\ `i3 <= m`) /\ (match x `0` y j2 i3))
  (Test5: true = true)
  (Test3: `i3 >= m`)
  ((`i3 >= m` ->
    ((result:Z)
     (result = j2 ->
      ((j:Z)
       (j = `j2 + 1` -> `0 <= j` /\
        (Zwf `0` `n - m + 1 - j` `n - m + 1 - j2`))) /\
      (match x `0` y j2 (array_length x)))))) /\
  ((`i3 < m` ->
    ((j:Z)
     (j = `j2 + 1` -> `0 <= j` /\ (Zwf `0` `n - m + 1 - j` `n - m + 1 - j2`))))).
Proof.
Intuition.
Unfold Zwf; Omega.
Assert i2=(array_length x). Omega. Subst i2; Assumption.
Unfold Zwf; Omega.
Save.

(* Why obligation from file "brute_force.c", characters 411-443 *)
Lemma BF_po_5 : 
  (m: Z)
  (n: Z)
  (x: (array Z))
  (y: (array Z))
  (Pre10: `(array_length x) = m` /\ `(array_length y) = n` /\ `0 <= n` /\
          `0 <= m`)
  (j1: Z)
  (Post1: j1 = `0`)
  (Variant1: Z)
  (j2: Z)
  (Pre9: Variant1 = `n - m + 1 - j2`)
  (Pre8: `0 <= j2`)
  (Test8: `j2 <= n - m`)
  (i2: Z)
  (Post2: i2 = `0`)
  (`0 <= i2` /\ `i2 <= m`) /\ (match x `0` y j2 i2).
Proof.
Intuition.
Subst i1; Apply match_empty; Auto with *.
Save.

(* Why obligation from file "brute_force.c", characters 307-313 *)
Lemma BF_po_6 : 
  (m: Z)
  (n: Z)
  (x: (array Z))
  (y: (array Z))
  (Pre10: `(array_length x) = m` /\ `(array_length y) = n` /\ `0 <= n` /\
          `0 <= m`)
  (j1: Z)
  (Post1: j1 = `0`)
  `0 <= j1`.
Proof.
Intuition.
Save.

