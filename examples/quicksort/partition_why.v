(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Export Partition.
Require Import Omega.
Require Import ZArithRing.


(* Why obligation from file "partition.mlw", characters 1340-1344 *)
Lemma swap_po_1 : 
  forall (i: Z),
  forall (j: Z),
  forall (t: (array Z)),
  forall (Pre5: (0 <= i /\ i < (array_length t)) /\ 0 <= j /\ j <
                (array_length t)),
  forall (Pre4: 0 <= i /\ i < (array_length t)),
  forall (v: Z),
  forall (Post3: v = (access t i)),
  forall (Pre2: 0 <= i /\ i < (array_length t)),
  0 <= j /\ j < (array_length t).
 Proof.
 tauto.
Qed.

(* Why obligation from file "partition.mlw", characters 1353-1362 *)
Lemma swap_po_2 : 
  forall (i: Z),
  forall (j: Z),
  forall (t: (array Z)),
  forall (Pre5: (0 <= i /\ i < (array_length t)) /\ 0 <= j /\ j <
                (array_length t)),
  forall (Pre4: 0 <= i /\ i < (array_length t)),
  forall (v: Z),
  forall (Post3: v = (access t i)),
  forall (Pre2: 0 <= i /\ i < (array_length t)),
  forall (Pre3: 0 <= j /\ j < (array_length t)),
  forall (t0: (array Z)),
  forall (Post1: t0 = (store t i (access t j))),
  0 <= j /\ j < (array_length t0).
Proof.
intuition.
intros; ArraySubst t0.
Qed.


(* Why obligation from file "partition.mlw", characters 1319-1371 *)
Lemma swap_po_3 : 
  forall (i: Z),
  forall (j: Z),
  forall (t: (array Z)),
  forall (Pre5: (0 <= i /\ i < (array_length t)) /\ 0 <= j /\ j <
                (array_length t)),
  forall (Pre4: 0 <= i /\ i < (array_length t)),
  forall (v: Z),
  forall (Post3: v = (access t i)),
  forall (Pre2: 0 <= i /\ i < (array_length t)),
  forall (Pre3: 0 <= j /\ j < (array_length t)),
  forall (t0: (array Z)),
  forall (Post1: t0 = (store t i (access t j))),
  forall (Pre1: 0 <= j /\ j < (array_length t0)),
  forall (t1: (array Z)),
  forall (Post2: t1 = (store t0 j v)),
  (exchange t1 t i j).
Proof.
intros; subst t1 t0 v.
auto with datatypes.
Qed.

(* Why obligation from file "partition.mlw", characters 1588-1592 *)
Lemma partition_po_1 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  0 <= l /\ l < (array_length t).
Proof.
intros; omega.
Qed.

(* Why obligation from file "partition.mlw", characters 1959-1964 *)
Lemma partition_po_2 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  forall (Variant3: Z),
  forall (i2: Z),
  forall (Pre8: Variant3 = (r - i2)),
  forall (Invi: (i1 <= i2 /\ i2 <= r) /\ (array_le t0 (l + 1) (i2 - 1) pv)),
  0 <= i2 /\ i2 < (array_length t0).
Proof.
intuition ArrayLength; omega.
Qed.

(* Why obligation from file "partition.mlw", characters 1974-1981 *)
Lemma partition_po_3 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  forall (Variant3: Z),
  forall (i2: Z),
  forall (Pre8: Variant3 = (r - i2)),
  forall (Invi: (i1 <= i2 /\ i2 <= r) /\ (array_le t0 (l + 1) (i2 - 1) pv)),
  forall (Pre7: 0 <= i2 /\ i2 < (array_length t0)),
  forall (Test3: (access t0 i2) <= pv),
  forall (result1: bool),
  forall (Bool2: (if result1 then i2 < j1 else i2 >= j1)),
  (if result1 then (access t0 i2) <= pv /\ i2 < j1 else (access t0 i2) >
   pv \/ (access t0 i2) <= pv /\ i2 >= j1).
Proof.
intuition.
induction result1; auto.
Qed.

(* Why obligation from file "partition.mlw", characters 1981-1981 *)
Lemma partition_po_4 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  forall (Variant3: Z),
  forall (i2: Z),
  forall (Pre8: Variant3 = (r - i2)),
  forall (Invi: (i1 <= i2 /\ i2 <= r) /\ (array_le t0 (l + 1) (i2 - 1) pv)),
  forall (Pre7: 0 <= i2 /\ i2 < (array_length t0)),
  forall (Test2: (access t0 i2) > pv),
  forall (result1: bool),
  forall (Post2: result1 = false),
  (if result1 then (access t0 i2) <= pv /\ i2 < j1 else (access t0 i2) >
   pv \/ (access t0 i2) <= pv /\ i2 >= j1).
Proof.
intuition.
induction result1; auto.
 discriminate Post2.
Qed.

(* Why obligation from file "partition.mlw", characters 2087-2098 *)
Lemma partition_po_5 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  forall (Variant3: Z),
  forall (i2: Z),
  forall (Pre8: Variant3 = (r - i2)),
  forall (Invi: (i1 <= i2 /\ i2 <= r) /\ (array_le t0 (l + 1) (i2 - 1) pv)),
  forall (Test5: (access t0 i2) <= pv /\ i2 < j1),
  forall (i3: Z),
  forall (Post1: i3 = (i2 + 1)),
  ((i1 <= i3 /\ i3 <= r) /\ (array_le t0 (l + 1) (i3 - 1) pv)) /\
  (Zwf 0 (r - i3) (r - i2)).
Proof.
intuition try discriminate.
omega.
omega.
replace (i3 - 1)%Z with (i2 - 1 + 1)%Z.
apply array_le_right_extension.
assumption.
ring (i2 - 1 + 1)%Z.
 assumption.
omega.
unfold Zwf; omega.
Qed.

(* Why obligation from file "partition.mlw", characters 2006-2057 *)
Lemma partition_po_6 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  (i1 <= i1 /\ i1 <= r) /\ (array_le t0 (l + 1) (i1 - 1) pv).
Proof.
intuition.
Qed.

(* Why obligation from file "partition.mlw", characters 2113-2118 *)
Lemma partition_po_7 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  forall (i2: Z),
  forall (Invi: ((i1 <= i2 /\ i2 <= r) /\
                (array_le t0 (l + 1) (i2 - 1) pv)) /\ ((access t0 i2) > pv \/
                (access t0 i2) <= pv /\ i2 >= j1)),
  forall (Variant5: Z),
  forall (j2: Z),
  forall (Pre15: Variant5 = j2),
  forall (Invj: (l <= j2 /\ j2 <= j1) /\ (array_ge t0 (j2 + 1) r pv)),
  0 <= j2 /\ j2 < (array_length t0).
Proof.
intuition ArrayLength; omega.
Qed.

(* Why obligation from file "partition.mlw", characters 2128-2135 *)
Lemma partition_po_8 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  forall (i2: Z),
  forall (Invi: ((i1 <= i2 /\ i2 <= r) /\
                (array_le t0 (l + 1) (i2 - 1) pv)) /\ ((access t0 i2) > pv \/
                (access t0 i2) <= pv /\ i2 >= j1)),
  forall (Variant5: Z),
  forall (j2: Z),
  forall (Pre15: Variant5 = j2),
  forall (Invj: (l <= j2 /\ j2 <= j1) /\ (array_ge t0 (j2 + 1) r pv)),
  forall (Pre14: 0 <= j2 /\ j2 < (array_length t0)),
  forall (Test7: (access t0 j2) >= pv),
  forall (result2: bool),
  forall (Bool4: (if result2 then i2 < j2 else i2 >= j2)),
  (if result2 then (access t0 j2) >= pv /\ i2 < j2 else (access t0 j2) <
   pv \/ (access t0 j2) >= pv /\ i2 >= j2).
 Proof.
 intuition.
induction result2; auto.
induction result2; auto.
Qed.

(* Why obligation from file "partition.mlw", characters 2135-2135 *)
Lemma partition_po_9 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  forall (i2: Z),
  forall (Invi: ((i1 <= i2 /\ i2 <= r) /\
                (array_le t0 (l + 1) (i2 - 1) pv)) /\ ((access t0 i2) > pv \/
                (access t0 i2) <= pv /\ i2 >= j1)),
  forall (Variant5: Z),
  forall (j2: Z),
  forall (Pre15: Variant5 = j2),
  forall (Invj: (l <= j2 /\ j2 <= j1) /\ (array_ge t0 (j2 + 1) r pv)),
  forall (Pre14: 0 <= j2 /\ j2 < (array_length t0)),
  forall (Test6: (access t0 j2) < pv),
  forall (result2: bool),
  forall (Post5: result2 = false),
  (if result2 then (access t0 j2) >= pv /\ i2 < j2 else (access t0 j2) <
   pv \/ (access t0 j2) >= pv /\ i2 >= j2).
Proof.
intuition.
induction result2; auto || discriminate Post5.
induction result2; auto || discriminate Post5.
Qed.

(* Why obligation from file "partition.mlw", characters 2231-2242 *)
Lemma partition_po_10 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  forall (i2: Z),
  forall (Invi: ((i1 <= i2 /\ i2 <= r) /\
                (array_le t0 (l + 1) (i2 - 1) pv)) /\ ((access t0 i2) > pv \/
                (access t0 i2) <= pv /\ i2 >= j1)),
  forall (Variant5: Z),
  forall (j2: Z),
  forall (Pre15: Variant5 = j2),
  forall (Invj: (l <= j2 /\ j2 <= j1) /\ (array_ge t0 (j2 + 1) r pv)),
  forall (Test9: (access t0 j2) >= pv /\ i2 < j2),
  forall (j3: Z),
  forall (Post4: j3 = (j2 - 1)),
  ((l <= j3 /\ j3 <= j1) /\ (array_ge t0 (j3 + 1) r pv)) /\ (Zwf 0 j3 j2).
Proof.
intuition.
apply array_ge_cons.
 intros j0 Hj0.
 elim (Z_le_gt_dec (j2 + 1) j0); intro.
elim H16; intros.
 apply H12; omega.
cut (j0 = j2); [ intro | omega ].
rewrite H12; omega.
apply array_ge_cons.
 intros j0 Hj0.
 omega.
Qed.

(* Why obligation from file "partition.mlw", characters 2154-2203 *)
Lemma partition_po_11 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  forall (i2: Z),
  forall (Invi: ((i1 <= i2 /\ i2 <= r) /\
                (array_le t0 (l + 1) (i2 - 1) pv)) /\ ((access t0 i2) > pv \/
                (access t0 i2) <= pv /\ i2 >= j1)),
  (l <= j1 /\ j1 <= j1) /\ (array_ge t0 (j1 + 1) r pv).
Proof.
intuition.
Qed.

(* Why obligation from file "partition.mlw", characters 2282-2296 *)
Lemma partition_po_12 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  forall (i2: Z),
  forall (Invi: ((i1 <= i2 /\ i2 <= r) /\
                (array_le t0 (l + 1) (i2 - 1) pv)) /\ ((access t0 i2) > pv \/
                (access t0 i2) <= pv /\ i2 >= j1)),
  forall (j2: Z),
  forall (Invj: ((l <= j2 /\ j2 <= j1) /\ (array_ge t0 (j2 + 1) r pv)) /\
                ((access t0 j2) < pv \/ (access t0 j2) >= pv /\ i2 >= j2)),
  forall (Test11: i2 < j2),
  (0 <= i2 /\ i2 < (array_length t0)) /\ 0 <= j2 /\ j2 < (array_length t0).
Proof.
intuition ArrayLength; omega.
Qed.

(* Why obligation from file "partition.mlw", characters 2267-2333 *)
Lemma partition_po_13 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  forall (i2: Z),
  forall (Invi: ((i1 <= i2 /\ i2 <= r) /\
                (array_le t0 (l + 1) (i2 - 1) pv)) /\ ((access t0 i2) > pv \/
                (access t0 i2) <= pv /\ i2 >= j1)),
  forall (j2: Z),
  forall (Invj: ((l <= j2 /\ j2 <= j1) /\ (array_ge t0 (j2 + 1) r pv)) /\
                ((access t0 j2) < pv \/ (access t0 j2) >= pv /\ i2 >= j2)),
  forall (Test11: i2 < j2),
  forall (Pre18: (0 <= i2 /\ i2 < (array_length t0)) /\ 0 <= j2 /\ j2 <
                 (array_length t0)),
  forall (t1: (array Z)),
  forall (Post25: (exchange t1 t0 i2 j2)),
  forall (i3: Z),
  forall (Post7: i3 = (i2 + 1)),
  forall (j3: Z),
  forall (Post8: j3 = (j2 - 1)),
  (((l + 1) <= i3 /\ i3 <= r) /\ j3 <= r /\
  (array_le t1 (l + 1) (i3 - 1) pv) /\ (array_ge t1 (j3 + 1) r pv) /\
  (sub_permut l r t1 t) /\ (access t1 l) = (access t l)) /\
  (Zwf 0 ((array_length t1) + 2 + j3 - i3) ((array_length t0) + 2 + j1 - i1)).
Proof.
intros.
decompose [and or] Invj; clear Invj.
 intuition unfold Zwf; ArrayLength; try omega.
replace (i3 - 1)%Z with (i2 - 1 + 1)%Z.
apply array_le_right_extension.
apply array_le_exchange with (t := t0) (x := i2) (y := j2).
omega.
 omega.
 assumption.
omega.
 apply exchange_sym; assumption.
ring (i2 - 1 + 1)%Z.
 elim Post25; intros.
 rewrite H26.
omega.
omega.
replace (j3 + 1)%Z with (j2 + 1 - 1)%Z.
apply array_ge_left_extension.
apply array_ge_exchange with (t := t0) (x := i2) (y := j2).
omega.
 generalize (sub_permut_length H20); intro; omega.
assumption.
 omega.
 apply exchange_sym; assumption.
ring (j2 + 1 - 1)%Z.
 elim Post25; intros.
 rewrite H27.
omega.
omega.
apply sub_permut_trans with (t' := t0).
apply exchange_is_sub_permut with (i := i2) (j := j2);
 [ omega | omega | assumption ].
assumption.
rewrite <- H23.
elim Post25; intros.
apply H28; omega.
absurd (i2 < j2)%Z; omega.
replace (j3 + 1)%Z with (j2 + 1 - 1)%Z.
apply array_ge_left_extension.
apply array_ge_exchange with (t := t0) (x := i2) (y := j2).
omega.
 intuition; generalize (sub_permut_length H21); intro; omega.
assumption.
 omega.
 apply exchange_sym; assumption.
ring (j2 + 1 - 1)%Z.
 elim Post25; intros.
 rewrite H28.
omega.
omega.
apply sub_permut_trans with (t' := t0).
apply exchange_is_sub_permut with (i := i2) (j := j2);
 [ omega | omega | assumption ].
assumption.
absurd (i2 < j2)%Z; omega.
Qed.

(* Why obligation from file "partition.mlw", characters 2333-2333 *)
Lemma partition_po_14 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Pre19: Variant1 = ((array_length t0) + 2 + j1 - i1)),
  forall (Inv: ((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)),
  forall (Test12: i1 < j1),
  forall (i2: Z),
  forall (Invi: ((i1 <= i2 /\ i2 <= r) /\
                (array_le t0 (l + 1) (i2 - 1) pv)) /\ ((access t0 i2) > pv \/
                (access t0 i2) <= pv /\ i2 >= j1)),
  forall (j2: Z),
  forall (Invj: ((l <= j2 /\ j2 <= j1) /\ (array_ge t0 (j2 + 1) r pv)) /\
                ((access t0 j2) < pv \/ (access t0 j2) >= pv /\ i2 >= j2)),
  forall (Test10: i2 >= j2),
  (((l + 1) <= i2 /\ i2 <= r) /\ j2 <= r /\
  (array_le t0 (l + 1) (i2 - 1) pv) /\ (array_ge t0 (j2 + 1) r pv) /\
  (sub_permut l r t0 t) /\ (access t0 l) = (access t l)) /\
  (Zwf 0 ((array_length t0) + 2 + j2 - i2) ((array_length t0) + 2 + j1 - i1)).
Proof.
intuition unfold Zwf; SameLength t t0; omega.
Qed.

(* Why obligation from file "partition.mlw", characters 1712-1892 *)
Lemma partition_po_15 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  ((l + 1) <= i /\ i <= r) /\ j <= r /\ (array_le t (l + 1) (i - 1) pv) /\
  (array_ge t (j + 1) r pv) /\ (sub_permut l r t t) /\ (access t l) =
  (access t l).
Proof.
intuition.
apply array_le_empty; omega.
apply array_ge_empty; omega.
Qed.

(* Why obligation from file "partition.mlw", characters 2356-2361 *)
Lemma partition_po_16 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Inv: (((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)) /\ i1 >= j1),
  0 <= i1 /\ i1 < (array_length t0).
Proof.
intuition SameLength t t0; omega.
Qed.

(* Why obligation from file "partition.mlw", characters 2386-2399 *)
Lemma partition_po_17 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Inv: (((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)) /\ i1 >= j1),
  forall (Pre30: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test14: (access t0 i1) < pv),
  (0 <= l /\ l < (array_length t0)) /\ 0 <= i1 /\ i1 < (array_length t0).
Proof.
intuition SameLength t t0; auto with *.
Qed.

(* Why obligation from file "partition.mlw", characters 2410-2412 *)
Lemma partition_po_18 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Inv: (((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)) /\ i1 >= j1),
  forall (Pre30: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test14: (access t0 i1) < pv),
  forall (Pre29: (0 <= l /\ l < (array_length t0)) /\ 0 <= i1 /\ i1 <
                 (array_length t0)),
  forall (t1: (array Z)),
  forall (Post34: (exchange t1 t0 l i1)),
  (l <= i1 /\ i1 <= r) /\ (partition_p t1 l r i1) /\ (sub_permut l r t1 t).
Proof.
intuition.
apply piv.
omega.
omega.
apply array_le_cons.
intros i0 Hi0.
 elim (Z_le_lt_eq_dec l i0); intros.
(* case l < i *)
elim Post34; intros.
elim H11; intros.
rewrite H22.
 rewrite (H23 i0).
 rewrite H18.
 rewrite <- Post11.
apply H24; omega.
omega.
omega.
omega.
(* case l = i *)
elim Post34; intros.
rewrite <- b.
 rewrite H21.
 rewrite H22.
rewrite H18.
omega.
omega.
(* array_ge *)
apply array_ge_cons.
intros j0 Hj0.
elim Post34; intros.
 rewrite H22.
rewrite H18.
rewrite (H23 j0).
elim H15; intros.
 rewrite <- Post11.
 apply H24; omega.
SameLength t1 t0; SameLength t0 t; omega.
omega.
omega.
(* (sub_permut l r t1 t) *)
apply sub_permut_trans with (t' := t0).
apply exchange_is_sub_permut with (i := l) (j := i1).
omega.
omega.
assumption.
assumption.
Qed.

(* Why obligation from file "partition.mlw", characters 2443-2462 *)
Lemma partition_po_19 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Inv: (((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)) /\ i1 >= j1),
  forall (Pre30: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test13: (access t0 i1) >= pv),
  (0 <= l /\ l < (array_length t0)) /\ 0 <= (i1 - 1) /\ (i1 - 1) <
  (array_length t0).
Proof.
intuition SameLength t0 t; omega.
Qed.

(* Why obligation from file "partition.mlw", characters 2472-2478 *)
Lemma partition_po_20 : 
  forall (l: Z),
  forall (r: Z),
  forall (t: (array Z)),
  forall (Pre32: (0 <= l /\ l < r) /\ r < (array_length t)),
  forall (Pre31: 0 <= l /\ l < (array_length t)),
  forall (pv: Z),
  forall (Post11: pv = (access t l)),
  forall (i: Z),
  forall (Post10: i = (l + 1)),
  forall (j: Z),
  forall (Post9: j = r),
  forall (i1: Z),
  forall (j1: Z),
  forall (t0: (array Z)),
  forall (Inv: (((l + 1) <= i1 /\ i1 <= r) /\ j1 <= r /\
               (array_le t0 (l + 1) (i1 - 1) pv) /\
               (array_ge t0 (j1 + 1) r pv) /\ (sub_permut l r t0 t) /\
               (access t0 l) = (access t l)) /\ i1 >= j1),
  forall (Pre30: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test13: (access t0 i1) >= pv),
  forall (Pre26: (0 <= l /\ l < (array_length t0)) /\ 0 <= (i1 - 1) /\
                 (i1 - 1) < (array_length t0)),
  forall (t1: (array Z)),
  forall (Post30: (exchange t1 t0 l (i1 - 1))),
  (l <= (i1 - 1) /\ (i1 - 1) <= r) /\ (partition_p t1 l r (i1 - 1)) /\
  (sub_permut l r t1 t).
Proof.
intuition.
apply piv.
omega.
omega.
(* array_le *)
apply array_le_cons.
intros i0 Hi0.
 elim (Z_le_lt_eq_dec l i0); intros.
(* case l < i *)
elim Post30; intros.
 rewrite H22.
rewrite H18.
rewrite (H23 i0).
 elim H11; intros.
 rewrite <- Post11.
 apply H24; omega.
omega.
omega.
omega.
(* case l = i *)
rewrite <- b.
 elim Post30; intros.
rewrite H22.
 rewrite H18.
rewrite H21.
elim H11; intros.
 rewrite <- Post11.
 apply H24; omega.
omega.
(* array_ge *)
apply array_ge_cons.
intro j0.
 ring (i1 - 1 + 1)%Z.
 intro Hj.
 elim Post30; intros.
rewrite H22.
 rewrite (H23 j0).
rewrite H18.
elim H15; intros.
 elim (Z_le_lt_eq_dec i1 j0); intros.
(* case i0 < j *)
rewrite <- Post11.
 apply H24; omega.
(* case i0 = j *)
rewrite <- b.
 omega.
omega.
SameLength t1 t0; SameLength t0 t; omega.
omega.
omega.
(* (sub_permut t1 t l r) *)
apply sub_permut_trans with (t' := t0).
apply exchange_is_sub_permut with (i := l) (j := Zpred i1).
omega.
unfold Zpred; omega.
assumption.
assumption.
Qed.


