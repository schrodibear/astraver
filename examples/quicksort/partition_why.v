(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Export Partition.
Require Omega.
Require ZArithRing.


(* Why obligation from file "partition.mlw", characters 1340-1344 *)
Lemma swap_po_1 : 
  (i: Z)
  (j: Z)
  (t: (array Z))
  (Pre5: (`0 <= i` /\ `i < (array_length t)`) /\ `0 <= j` /\
         `j < (array_length t)`)
  (Pre4: `0 <= i` /\ `i < (array_length t)`)
  (v: Z)
  (Post3: v = (access t i))
  (Pre2: `0 <= i` /\ `i < (array_length t)`)
  `0 <= j` /\ `j < (array_length t)`.
Proof. 
Tauto.
Save.

(* Why obligation from file "partition.mlw", characters 1353-1362 *)
Lemma swap_po_2 : 
  (i: Z)
  (j: Z)
  (t: (array Z))
  (Pre5: (`0 <= i` /\ `i < (array_length t)`) /\ `0 <= j` /\
         `j < (array_length t)`)
  (Pre4: `0 <= i` /\ `i < (array_length t)`)
  (v: Z)
  (Post3: v = (access t i))
  (Pre2: `0 <= i` /\ `i < (array_length t)`)
  (Pre3: `0 <= j` /\ `j < (array_length t)`)
  (t0: (array Z))
  (Post1: t0 = (store t i (access t j)))
  `0 <= j` /\ `j < (array_length t0)`.
Proof.
Intuition.
Intros; ArraySubst t0.
Save.


(* Why obligation from file "partition.mlw", characters 1319-1371 *)
Lemma swap_po_3 : 
  (i: Z)
  (j: Z)
  (t: (array Z))
  (Pre5: (`0 <= i` /\ `i < (array_length t)`) /\ `0 <= j` /\
         `j < (array_length t)`)
  (Pre4: `0 <= i` /\ `i < (array_length t)`)
  (v: Z)
  (Post3: v = (access t i))
  (Pre2: `0 <= i` /\ `i < (array_length t)`)
  (Pre3: `0 <= j` /\ `j < (array_length t)`)
  (t0: (array Z))
  (Post1: t0 = (store t i (access t j)))
  (Pre1: `0 <= j` /\ `j < (array_length t0)`)
  (t1: (array Z))
  (Post2: t1 = (store t0 j v))
  (exchange t1 t i j).
Proof.
Intros; Subst t1 t0 v.
Auto with datatypes.
Save.

(* Why obligation from file "partition.mlw", characters 1579-1583 *)
Lemma partition_po_1 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  `0 <= l` /\ `l < (array_length t)`.
Proof.
Intros; Omega.
Save.

(* Why obligation from file "partition.mlw", characters 1950-1955 *)
Lemma partition_po_2 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (Variant3: Z)
  (i2: Z)
  (Pre8: Variant3 = `r - i2`)
  (Invi: (`i1 <= i2` /\ `i2 <= r`) /\ (array_le t0 `l + 1` `i2 - 1` pv))
  `0 <= i2` /\ `i2 < (array_length t0)`.
Proof.
Intuition (ArrayLength; Omega).
Save.

(* Why obligation from file "partition.mlw", characters 1965-1972 *)
Lemma partition_po_3 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (Variant3: Z)
  (i2: Z)
  (Pre8: Variant3 = `r - i2`)
  (Invi: (`i1 <= i2` /\ `i2 <= r`) /\ (array_le t0 `l + 1` `i2 - 1` pv))
  (Pre7: `0 <= i2` /\ `i2 < (array_length t0)`)
  (Test3: `(access t0 i2) <= pv`)
  (result1: bool)
  (Bool2: (if result1 then `i2 < j1` else `i2 >= j1`))
  (if result1 then `(access t0 i2) <= pv` /\ `i2 < j1` \/
   `(access t0 i2) > pv` /\ true = false else `(access t0 i2) <= pv` /\
   `i2 >= j1` \/ `(access t0 i2) > pv` /\ false = false).
Proof.
Intuition.
Induction result1; Auto.
Save.

(* Why obligation from file "partition.mlw", characters 1950-1972 *)
Lemma partition_po_4 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (Variant3: Z)
  (i2: Z)
  (Pre8: Variant3 = `r - i2`)
  (Invi: (`i1 <= i2` /\ `i2 <= r`) /\ (array_le t0 `l + 1` `i2 - 1` pv))
  (Pre7: `0 <= i2` /\ `i2 < (array_length t0)`)
  (Test2: `(access t0 i2) > pv`)
  (result1: bool)
  (Post2: result1 = false)
  (if result1 then `(access t0 i2) <= pv` /\ `i2 < j1` \/
   `(access t0 i2) > pv` /\ true = false else `(access t0 i2) <= pv` /\
   `i2 >= j1` \/ `(access t0 i2) > pv` /\ false = false).
Proof.
Intuition.
Induction result1; Auto.
Save.

(* Why obligation from file "partition.mlw", characters 1944-2095 *)
Lemma partition_po_5 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (Variant3: Z)
  (i2: Z)
  (Pre8: Variant3 = `r - i2`)
  (Invi: (`i1 <= i2` /\ `i2 <= r`) /\ (array_le t0 `l + 1` `i2 - 1` pv))
  (Test5: `(access t0 i2) <= pv` /\ `i2 < j1` \/ `(access t0 i2) > pv` /\
          true = false)
  (i3: Z)
  (Post1: i3 = `i2 + 1`)
  ((`i1 <= i3` /\ `i3 <= r`) /\ (array_le t0 `l + 1` `i3 - 1` pv)) /\
  (Zwf `0` `r - i3` `r - i2`).
Proof.
Intuition Try Discriminate.
Omega.
Omega.
Replace `i3-1` with `(i2-1)+1`.
Apply array_le_right_extension.
Assumption.
Ring `(i2-1+1)`. Assumption.
Omega.
Unfold Zwf; Omega.
Save.

(* Why obligation from file "partition.mlw", characters 1997-2048 *)
Lemma partition_po_6 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (`i1 <= i1` /\ `i1 <= r`) /\ (array_le t0 `l + 1` `i1 - 1` pv).
Proof.
Intuition.
Save.

(* Why obligation from file "partition.mlw", characters 2104-2109 *)
Lemma partition_po_7 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (i2: Z)
  (Invi: ((`i1 <= i2` /\ `i2 <= r`) /\ (array_le t0 `l + 1` `i2 - 1` pv)) /\
         (`(access t0 i2) <= pv` /\ `i2 >= j1` \/ `(access t0 i2) > pv` /\
         false = false))
  (Variant5: Z)
  (j2: Z)
  (Pre15: Variant5 = j2)
  (Invj: (`l <= j2` /\ `j2 <= j1`) /\ (array_ge t0 `j2 + 1` r pv))
  `0 <= j2` /\ `j2 < (array_length t0)`.
Proof.
Intuition (ArrayLength; Omega).
Save.

(* Why obligation from file "partition.mlw", characters 2119-2126 *)
Lemma partition_po_8 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (i2: Z)
  (Invi: ((`i1 <= i2` /\ `i2 <= r`) /\ (array_le t0 `l + 1` `i2 - 1` pv)) /\
         (`(access t0 i2) <= pv` /\ `i2 >= j1` \/ `(access t0 i2) > pv` /\
         false = false))
  (Variant5: Z)
  (j2: Z)
  (Pre15: Variant5 = j2)
  (Invj: (`l <= j2` /\ `j2 <= j1`) /\ (array_ge t0 `j2 + 1` r pv))
  (Pre14: `0 <= j2` /\ `j2 < (array_length t0)`)
  (Test7: `(access t0 j2) >= pv`)
  (result2: bool)
  (Bool4: (if result2 then `i2 < j2` else `i2 >= j2`))
  (if result2 then `(access t0 j2) >= pv` /\ `i2 < j2` \/
   `(access t0 j2) < pv` /\ true = false else `(access t0 j2) >= pv` /\
   `i2 >= j2` \/ `(access t0 j2) < pv` /\ false = false).
Proof. 
Intuition.
Induction result2; Auto.
Induction result2; Auto.
Save.

(* Why obligation from file "partition.mlw", characters 2104-2126 *)
Lemma partition_po_9 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (i2: Z)
  (Invi: ((`i1 <= i2` /\ `i2 <= r`) /\ (array_le t0 `l + 1` `i2 - 1` pv)) /\
         (`(access t0 i2) <= pv` /\ `i2 >= j1` \/ `(access t0 i2) > pv` /\
         false = false))
  (Variant5: Z)
  (j2: Z)
  (Pre15: Variant5 = j2)
  (Invj: (`l <= j2` /\ `j2 <= j1`) /\ (array_ge t0 `j2 + 1` r pv))
  (Pre14: `0 <= j2` /\ `j2 < (array_length t0)`)
  (Test6: `(access t0 j2) < pv`)
  (result2: bool)
  (Post5: result2 = false)
  (if result2 then `(access t0 j2) >= pv` /\ `i2 < j2` \/
   `(access t0 j2) < pv` /\ true = false else `(access t0 j2) >= pv` /\
   `i2 >= j2` \/ `(access t0 j2) < pv` /\ false = false).
Proof.
Intuition.
Induction result2; Auto.
Induction result2; Auto.
Save.

(* Why obligation from file "partition.mlw", characters 2098-2239 *)
Lemma partition_po_10 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (i2: Z)
  (Invi: ((`i1 <= i2` /\ `i2 <= r`) /\ (array_le t0 `l + 1` `i2 - 1` pv)) /\
         (`(access t0 i2) <= pv` /\ `i2 >= j1` \/ `(access t0 i2) > pv` /\
         false = false))
  (Variant5: Z)
  (j2: Z)
  (Pre15: Variant5 = j2)
  (Invj: (`l <= j2` /\ `j2 <= j1`) /\ (array_ge t0 `j2 + 1` r pv))
  (Test9: `(access t0 j2) >= pv` /\ `i2 < j2` \/ `(access t0 j2) < pv` /\
          true = false)
  (j3: Z)
  (Post4: j3 = `j2 - 1`)
  ((`l <= j3` /\ `j3 <= j1`) /\ (array_ge t0 `j3 + 1` r pv)) /\
  (Zwf `0` j3 j2).
Proof.
Intuition.
Apply array_ge_cons. Intros j0 Hj0. Omega.
Discriminate H21.
Discriminate H21.
Apply array_ge_cons. Intros j0 Hj0. 
Elim (Z_le_gt_dec `j2+1` j0); Intro.
Elim H17; Intros. Apply H13; Omega.
Cut `j0 = j2`; [ Intro | Omega ].
Rewrite H13; Omega.
Discriminate H21.
Discriminate H21.
Save.

(* Why obligation from file "partition.mlw", characters 2145-2194 *)
Lemma partition_po_11 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (i2: Z)
  (Invi: ((`i1 <= i2` /\ `i2 <= r`) /\ (array_le t0 `l + 1` `i2 - 1` pv)) /\
         (`(access t0 i2) <= pv` /\ `i2 >= j1` \/ `(access t0 i2) > pv` /\
         false = false))
  (`l <= j1` /\ `j1 <= j1`) /\ (array_ge t0 `j1 + 1` r pv).
Proof.
Intuition.
Save.

(* Why obligation from file "partition.mlw", characters 2273-2287 *)
Lemma partition_po_12 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (i2: Z)
  (Invi: ((`i1 <= i2` /\ `i2 <= r`) /\ (array_le t0 `l + 1` `i2 - 1` pv)) /\
         (`(access t0 i2) <= pv` /\ `i2 >= j1` \/ `(access t0 i2) > pv` /\
         false = false))
  (j2: Z)
  (Invj: ((`l <= j2` /\ `j2 <= j1`) /\ (array_ge t0 `j2 + 1` r pv)) /\
         (`(access t0 j2) >= pv` /\ `i2 >= j2` \/ `(access t0 j2) < pv` /\
         false = false))
  (Test11: `i2 < j2`)
  (`0 <= i2` /\ `i2 < (array_length t0)`) /\ `0 <= j2` /\
  `j2 < (array_length t0)`.
Proof.
Intuition (ArrayLength; Omega).
Save.

(* Why obligation from file "partition.mlw", characters 2258-2324 *)
Lemma partition_po_13 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (i2: Z)
  (Invi: ((`i1 <= i2` /\ `i2 <= r`) /\ (array_le t0 `l + 1` `i2 - 1` pv)) /\
         (`(access t0 i2) <= pv` /\ `i2 >= j1` \/ `(access t0 i2) > pv` /\
         false = false))
  (j2: Z)
  (Invj: ((`l <= j2` /\ `j2 <= j1`) /\ (array_ge t0 `j2 + 1` r pv)) /\
         (`(access t0 j2) >= pv` /\ `i2 >= j2` \/ `(access t0 j2) < pv` /\
         false = false))
  (Test11: `i2 < j2`)
  (Pre18: (`0 <= i2` /\ `i2 < (array_length t0)`) /\ `0 <= j2` /\
          `j2 < (array_length t0)`)
  (t1: (array Z))
  (Post25: (exchange t1 t0 i2 j2))
  (i3: Z)
  (Post7: i3 = `i2 + 1`)
  (j3: Z)
  (Post8: j3 = `j2 - 1`)
  ((`l + 1 <= i3` /\ `i3 <= r`) /\ `j3 <= r` /\
  (array_le t1 `l + 1` `i3 - 1` pv) /\ (array_ge t1 `j3 + 1` r pv) /\
  (sub_permut l r t1 t) /\ `(access t1 l) = (access t l)`) /\
  (Zwf `0` `(array_length t1) + 2 + j3 - i3` `(array_length t0) + 2 + j1 - i1`).
Proof.
Intros.
Decompose [and or] Invj; Clear Invj. 
Absurd `i2 < j2`; Omega.
Repeat (Apply conj); Try Omega.
Replace `i3-1` with `(i2-1)+1`.
Apply array_le_right_extension.
Decompose [and] Invi. Apply array_le_exchange with t:=t0 x:=i2 y:=j2.
Omega. Omega. 
Assumption. Omega. Apply exchange_sym; Assumption.
Ring `(i2-1+1)`. Elim Post25; Intros. Rewrite H7.
Omega.
Omega.
(* (array_ge t1 `(Zpred j1)+1` r (#t[l])) *)
Replace `j3+1` with `(j2+1)-1`.
Apply array_ge_left_extension.
Apply array_ge_exchange with t:=t0 x:=i2 y:=j2.
Omega. 
Intuition; Generalize (sub_permut_length H21); Intro; Omega.
Assumption. Omega. Apply exchange_sym; Assumption.
Ring `(j2+1-1)`. Elim Post25; Intros. Rewrite H8.
Omega.
Omega.
(* (sub_permut l r t1 t) *)
Apply sub_permut_trans with t':=t0.
Apply exchange_is_sub_permut with i:=i2 j:=j2; [Omega | Omega | Assumption].
Decompose [and] Inv; Assumption.
(* (access t1 l) = (access t l) *)
Decompose [and] Inv. Rewrite <- H11.
Elim Post25; Intros.
Apply H16; Omega.
Unfold Zwf; ArrayLength; Omega.
Save.

(* Why obligation from file "partition.mlw", characters 2242-2324 *)
Lemma partition_po_14 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (Variant1: Z)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Pre19: Variant1 = `(array_length t0) + 2 + j1 - i1`)
  (Inv: (`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`)
  (Test12: `i1 < j1`)
  (i2: Z)
  (Invi: ((`i1 <= i2` /\ `i2 <= r`) /\ (array_le t0 `l + 1` `i2 - 1` pv)) /\
         (`(access t0 i2) <= pv` /\ `i2 >= j1` \/ `(access t0 i2) > pv` /\
         false = false))
  (j2: Z)
  (Invj: ((`l <= j2` /\ `j2 <= j1`) /\ (array_ge t0 `j2 + 1` r pv)) /\
         (`(access t0 j2) >= pv` /\ `i2 >= j2` \/ `(access t0 j2) < pv` /\
         false = false))
  (Test10: `i2 >= j2`)
  ((`l + 1 <= i2` /\ `i2 <= r`) /\ `j2 <= r` /\
  (array_le t0 `l + 1` `i2 - 1` pv) /\ (array_ge t0 `j2 + 1` r pv) /\
  (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`) /\
  (Zwf `0` `(array_length t0) + 2 + j2 - i2` `(array_length t0) + 2 + j1 - i1`).
Proof.
Intuition (Unfold Zwf; SameLength t t0; Omega).
Save.

(* Why obligation from file "partition.mlw", characters 1703-1883 *)
Lemma partition_po_15 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (`l + 1 <= i` /\ `i <= r`) /\ `j <= r` /\
  (array_le t `l + 1` `i - 1` pv) /\ (array_ge t `j + 1` r pv) /\
  (sub_permut l r t t) /\ `(access t l) = (access t l)`.
Proof.
Intuition.
Apply array_le_empty; Omega.
Apply array_ge_empty; Omega.
Save.

(* Why obligation from file "partition.mlw", characters 2347-2352 *)
Lemma partition_po_16 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Inv: ((`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`) /\
        `i1 >= j1`)
  `0 <= i1` /\ `i1 < (array_length t0)`.
Proof.
Intuition (SameLength t t0; Omega).
Save.

(* Why obligation from file "partition.mlw", characters 2377-2390 *)
Lemma partition_po_17 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Inv: ((`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`) /\
        `i1 >= j1`)
  (Pre30: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test14: `(access t0 i1) < pv`)
  (`0 <= l` /\ `l < (array_length t0)`) /\ `0 <= i1` /\
  `i1 < (array_length t0)`.
Proof.
Intuition (SameLength t t0; Auto with *).
Save.

(* Why obligation from file "partition.mlw", characters 2401-2403 *)
Lemma partition_po_18 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Inv: ((`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`) /\
        `i1 >= j1`)
  (Pre30: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test14: `(access t0 i1) < pv`)
  (Pre29: (`0 <= l` /\ `l < (array_length t0)`) /\ `0 <= i1` /\
          `i1 < (array_length t0)`)
  (t1: (array Z))
  (Post34: (exchange t1 t0 l i1))
  (`l <= i1` /\ `i1 <= r`) /\ (partition_p t1 l r i1) /\
  (sub_permut l r t1 t).
Proof.
Intuition.
Apply piv.
Omega.
Omega.
Apply array_le_cons.
Intros i0 Hi0. Elim (Z_le_lt_eq_dec l i0); Intros.
(* case l < i *)
Elim Post34; Intros.
Elim H11; Intros.
Rewrite H22. 
Rewrite (H23 i0). Rewrite H18. Rewrite <- Post11.
Apply H24; Omega.
Omega.
Omega.
Omega.
(* case l = i *)
Elim Post34; Intros.
Rewrite <- b. Rewrite H21. Rewrite H22.
Rewrite H18.
Omega.
Omega.
(* array_ge *)
Apply array_ge_cons.
Intros j0 Hj0.
Elim Post34; Intros. Rewrite H22.
Rewrite H18.
Rewrite (H23 j0).
Elim H15; Intros. Rewrite <- Post11. Apply H24; Omega.
SameLength t1 t0; SameLength t0 t; Omega.
Omega.
Omega.
(* (sub_permut l r t1 t) *)
Apply sub_permut_trans with t':=t0.
Apply exchange_is_sub_permut with i:=l j:=i1.
Omega.
Omega.
Assumption.
Assumption.
Save.

(* Why obligation from file "partition.mlw", characters 2434-2453 *)
Lemma partition_po_19 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Inv: ((`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`) /\
        `i1 >= j1`)
  (Pre30: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test13: `(access t0 i1) >= pv`)
  (`0 <= l` /\ `l < (array_length t0)`) /\ `0 <= i1 - 1` /\
  `i1 - 1 < (array_length t0)`.
Proof.
Intuition (SameLength t0 t; Omega).
Save.

(* Why obligation from file "partition.mlw", characters 2463-2469 *)
Lemma partition_po_20 : 
  (l: Z)
  (r: Z)
  (t: (array Z))
  (Pre32: (`0 <= l` /\ `l < r`) /\ `r < (array_length t)`)
  (Pre31: `0 <= l` /\ `l < (array_length t)`)
  (pv: Z)
  (Post11: pv = (access t l))
  (i: Z)
  (Post10: i = `l + 1`)
  (j: Z)
  (Post9: j = r)
  (i1: Z)
  (j1: Z)
  (t0: (array Z))
  (Inv: ((`l + 1 <= i1` /\ `i1 <= r`) /\ `j1 <= r` /\
        (array_le t0 `l + 1` `i1 - 1` pv) /\ (array_ge t0 `j1 + 1` r pv) /\
        (sub_permut l r t0 t) /\ `(access t0 l) = (access t l)`) /\
        `i1 >= j1`)
  (Pre30: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test13: `(access t0 i1) >= pv`)
  (Pre26: (`0 <= l` /\ `l < (array_length t0)`) /\ `0 <= i1 - 1` /\
          `i1 - 1 < (array_length t0)`)
  (t1: (array Z))
  (Post30: (exchange t1 t0 l `i1 - 1`))
  (`l <= i1 - 1` /\ `i1 - 1 <= r`) /\ (partition_p t1 l r `i1 - 1`) /\
  (sub_permut l r t1 t).
Proof.
Intuition.
Apply piv.
Omega.
Omega.
(* array_le *)
Apply array_le_cons.
Intros i0 Hi0. 
Elim (Z_le_lt_eq_dec l i0); Intros.
(* case l < i *)
Elim Post30; Intros. Rewrite H22.
Rewrite H18.
Rewrite (H23 i0). Elim H11; Intros. 
Rewrite <- Post11. Apply H24; Omega.
Omega.
Omega.
Omega.
(* case l = i *)
Rewrite <- b. 
Elim Post30; Intros.
Rewrite H22. Rewrite H18.
Rewrite H21.
Elim H11; Intros. 
Rewrite <- Post11. Apply H24; Omega.
Omega.
(* array_ge *)
Apply array_ge_cons.
Intro j0. Ring `i1-1+1`. Intro Hj. 
Elim Post30; Intros.
Rewrite H22. Rewrite (H23 j0).
Rewrite H18.
Elim H15; Intros. 
Elim (Z_le_lt_eq_dec i1 j0); Intros.
(* case i0 < j *)
Rewrite <- Post11. Apply H24; Omega.
(* case i0 = j *)
Rewrite <- b. Omega.
Omega.
SameLength t1 t0; SameLength t0 t; Omega.
Omega.
Omega.
(* (sub_permut t1 t l r) *)
Apply sub_permut_trans with t':=t0.
Apply exchange_is_sub_permut with i:=l j:=(Zpred i1).
Omega.
Unfold Zpred; Omega.
Assumption.
Assumption.
Save.


