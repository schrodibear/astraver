
Require Why.
Require Omega.

Parameter foo : Set.

(*Why*) Parameter v2 : Z.

(*Why*) Parameter v3 : Z.

(*Why*) Parameter v5 : foo.

(*Why*) Parameter f1 : (_: Z)(_: bool)Z.

(*Why*) Parameter f2 : (_: Z)bool.

(*Why*) Parameter f3 :
  (x: Z)(y: Z)(_: `x >= 0`)
  (sig_2 Z Z [y0: Z][result: Z](`y0 = y + x + result`)).

(*Why*) Parameter f4 : (_: unit)unit.

(*Why*) Parameter f5 : (_: foo)foo.

(*Why*) Parameter f6 : (x: foo)foo.

(*Why*) Parameter f7 : (x: foo)foo.

(*Why*) Parameter f8 :
  (t: (array `10` Z))(sig_1 unit [result: unit](`(access t 1) = 2`)).




Definition p1 := (* validation *)
  (exist_1 [result: Z]True `0` I).

Lemma p2_po_1 : 
  ~False.
Proof.
Tauto.
Save.




Definition p2 := (* validation *)
  (exist_1 [result: Z]~False `0` p2_po_1).

Lemma p3_po_1 : 
  True /\ True.
Proof.
Tauto.
Save.




Definition p3 := (* validation *)
  (exist_1 [result: Z]True /\ True `0` p3_po_1).

Lemma p4_po_1 : 
  True \/ False.
Proof.
Tauto.
Save.




Definition p4 := (* validation *)
  (exist_1 [result: Z]True \/ False `0` p4_po_1).

Lemma p5_po_1 : 
  False \/ ~False.
Proof. 
Auto.
Save.




Definition p5 := (* validation *)
  (exist_1 [result: Z]False \/ ~False `0` p5_po_1).

Lemma p6_po_1 : 
  (True -> ~False).
Proof.
Auto.
Save.




Definition p6 := (* validation *)
  (exist_1 [result: Z](True -> ~False) `0` p6_po_1).

Lemma p7_po_1 : 
  ((x:Z) `x = x`).
Proof.
Auto.
Save.




Definition p7 := (* validation *)
  (exist_1 [result: Z]((x:Z) `x = x`) `0` p7_po_1).

Lemma p8_po_1 : 
  True /\ ((x:Z) `x = x`).
Proof.
Auto.
Save.




Definition p8 := (* validation *)
  (exist_1 [result: Z]True /\ ((x:Z) `x = x`) `0` p8_po_1).

Lemma p9_po_1 : 
  ((x:Z) ((y:Z) (`x = y` -> `x = y`))).
Proof.
Auto.
Save.


































Definition p9 := (* validation *)
  (exist_1 [result: Z]((x:Z) ((y:Z) (`x = y` -> `x = y`))) `0` p9_po_1).

Definition acc1 := (* validation *)
  v2.

Definition acc2 := (* validation *)
  acc1.

Definition acc3 := (* validation *)
  f8.

Definition d1 := (* validation *)
  [v1: bool]v1.

Definition d2 := (* validation *)
  [v4: Z]v4.

Definition ar1 := (* validation *)
  `1`.

Definition ar2 := (* validation *)
  `(-1)`.

Definition ar3 := (* validation *)
  `1 + 1`.

Definition ar4 := (* validation *)
  `1 - 1`.

Definition ar5 := (* validation *)
  `1 * 1`.

Lemma ar6_po_1 : 
  ~(`1` = `0`).
Proof.
Omega.
Save.




Definition ar6 := (* validation *)
  let Pre1 = ar6_po_1 in
  (Zdiv `1` `1`).

Lemma ar7_po_1 : 
  ~(`1` = `0`).
Proof.
Omega.
Save.





















































































Definition ar7 := (* validation *)
  let Pre1 = ar7_po_1 in
  (Zmod `1` `1`).

Definition a1 := (* validation *)
  [v4: Z]
    let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
      (refl_equal ? `1`)) in
    (exist_2 [v10: Z][result0: unit]v10 = `1` result tt Post1).

Definition a2 := (* validation *)
  [v1: bool]
    let (result, Post1) = (exist_1 [result: bool]result = true true
      (refl_equal ? true)) in
    (exist_2 [v10: bool][result0: unit]v10 = true result tt Post1).

Definition a3 := (* validation *)
  [v4: Z]
    let (result, Post1) = (exist_1 [result: Z]result = `2 + 2` `2 + 2`
      (refl_equal ? `2 + 2`)) in
    (exist_2 [v10: Z][result0: unit]v10 = `2 + 2` result tt Post1).

Definition a4 := (* validation *)
  [v4: Z]
    let (result, Post1) = (exist_1 [result: Z]result = v4 v4
      (refl_equal ? v4)) in
    (exist_2 [v10: Z][result0: unit]v10 = v4 result tt Post1).

Definition s1 := (* validation *)
  [v4: Z]
    let (v9, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
        (refl_equal ? `1`)) in
      (exist_2 [v10: Z][result0: unit]v10 = `1` result tt Post1) in
    let (v10, result0, Post2) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = `2` `2`
        (refl_equal ? `2`)) in
      (exist_2 [v11: Z][result1: unit]v11 = `2` result0 tt Post2) in
    (Build_tuple_2 v10 result0).

Definition s2 := (* validation *)
  [v1: bool; v4: Z]
    let (v9, result, Post1) =
      let (result, Post1) = (exist_1 [result: bool]result = true true
        (refl_equal ? true)) in
      (exist_2 [v10: bool][result0: unit]v10 = true result tt Post1) in
    let (v10, result0, Post2) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = `2` `2`
        (refl_equal ? `2`)) in
      (exist_2 [v11: Z][result1: unit]v11 = `2` result0 tt Post2) in
    (Build_tuple_3 v9 v10 result0).

Definition s3 := (* validation *)
  [v4: Z]
    let (v9, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
        (refl_equal ? `1`)) in
      (exist_2 [v10: Z][result0: unit]v10 = `1` result tt Post1) in
    let (v10, result0, Post2) =
      let (result0, Post2) = (exist_1 [result0: Z]result0 = v9 v9
        (refl_equal ? v9)) in
      (exist_2 [v11: Z][result1: unit]v11 = v9 result0 tt Post2) in
    let (v11, result1, Post3) =
      let (result1, Post3) = (exist_1 [result1: Z]result1 = `3` `3`
        (refl_equal ? `3`)) in
      (exist_2 [v12: Z][result2: unit]v12 = `3` result1 tt Post3) in
    (Build_tuple_2 v11 result1).

Definition s4 := (* validation *)
  [v4: Z]
    let (v9, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
        (refl_equal ? `1`)) in
      (exist_2 [v10: Z][result0: unit]v10 = `1` result tt Post1) in
    (Build_tuple_2 v9 `2`).

Definition c1 := (* validation *)
  let (result, Post1) = (exist_1 [result: bool]result = true true
    (refl_equal ? true)) in
  (Cases (btest [result:bool]result = true result Post1) of
  | (left Test2) => `1`
  | (right Test1) => `2` end).

Definition c2 := (* validation *)
  [v1: bool]
    let (result, Post1) = (exist_1 [result: bool]result = v1 v1
      (refl_equal ? v1)) in
    (Cases (btest [result:bool]result = v1 result Post1) of
    | (left Test2) => `1`
    | (right Test1) => `2` end).

Definition c3 := (* validation *)
  [v4: Z]
    let (result, Bool1) =
      let (result1, Post4) = (Z_eq_bool v4 `1`) in
      (exist_1 [result2: bool]
      (if result2 then `v4 = 1` else `v4 <> 1`) result1 Post4) in
    (Cases (btest [result:bool](if result then `v4 = 1` else `v4 <> 1`)
            result Bool1) of
    | (left Test2) =>
        let (v9, result0, Post1) =
          let (result0, Post1) = (exist_1 [result0: Z]result0 = `2` `2`
            (refl_equal ? `2`)) in
          (exist_2 [v10: Z][result1: unit]v10 = `2` result0 tt Post1) in
        (Build_tuple_2 v9 result0)
    | (right Test1) =>
        let (v9, result0, Post2) =
          let (result0, Post2) = (exist_1 [result0: Z]result0 = `3` `3`
            (refl_equal ? `3`)) in
          (exist_2 [v10: Z][result1: unit]v10 = `3` result0 tt Post2) in
        (Build_tuple_2 v9 result0) end).

Definition l1 := (* validation *)
  let (x, Post1) = (exist_1 [result: Z]result = `1` `1`
    (refl_equal ? `1`)) in
  x.

Definition l2 := (* validation *)
  [v4: Z]
    let (x, Post2) = (exist_1 [result: Z]result = `1` `1`
      (refl_equal ? `1`)) in
    let (v9, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = x x
        (refl_equal ? x)) in
      (exist_2 [v10: Z][result0: unit]v10 = x result tt Post1) in
    (Build_tuple_2 v9 result).

Definition l3 := (* validation *)
  let (x, Post2) = (exist_1 [result: Z]result = `1` `1`
    (refl_equal ? `1`)) in
  let result =
    let (y, Post1) = (exist_1 [result: Z]result = `2` `2`
      (refl_equal ? `2`)) in
    `x + y` in
  result.

Definition l4 := (* validation *)
  [v4: Z]
    let result =
      let (x, Post1) = (exist_1 [result: Z]result = `1` `1`
        (refl_equal ? `1`)) in
      `1` in
    (Build_tuple_2 result tt).

Definition l5 := (* validation *)
  [v1: bool; v4: Z]
    let (x, Post3) = (exist_1 [result: Z]result = `1` `1`
      (refl_equal ? `1`)) in
    let (v10, v9, result) =
      let (v9, result, Post1) =
        let (result, Post1) = (exist_1 [result: bool]result = true true
          (refl_equal ? true)) in
        (exist_2 [v10: bool][result0: unit]v10 = true result tt Post1) in
      let (v10, result0, Post2) =
        let (result0, Post2) = (exist_1 [result0: Z]result0 = x x
          (refl_equal ? x)) in
        (exist_2 [v11: Z][result1: unit]v11 = x result0 tt Post2) in
      (Build_tuple_3 v9 v10 result0) in
    (Build_tuple_3 v10 v9 result).

Definition lr1 := (* validation *)
  let (result, Post2) = (exist_1 [result: Z]result = `1` `1`
    (refl_equal ? `1`)) in
  let (x0, result0, Post1) =
    let (result0, Post1) = (exist_1 [result0: Z]result0 = `2` `2`
      (refl_equal ? `2`)) in
    (exist_2 [x1: Z][result1: unit]x1 = `2` result0 tt Post1) in
  result0.

Definition lr2 := (* validation *)
  let (result, Post2) = (exist_1 [result: Z]result = `1` `1`
    (refl_equal ? `1`)) in
  let (x0, result0) =
    let (x0, result0, Post1) =
      let (result0, Post1) = (exist_1 [result0: Z]
        result0 = `result + 1` `result + 1` (refl_equal ? `result + 1`)) in
      (exist_2 [x1: Z][result1: unit]x1 = `result + 1` result0 tt Post1) in
    (Build_tuple_2 x0 x0) in
  result0.

Definition lr3 := (* validation *)
  let (result, Post3) = (exist_1 [result: Z]result = `1` `1`
    (refl_equal ? `1`)) in
  let (x0, result0) =
    let (result0, Post2) = (exist_1 [result0: Z]result0 = result result
      (refl_equal ? result)) in
    let (x0, result1, Post1) =
      let (result1, Post1) = (exist_1 [result1: Z]result1 = result0 result0
        (refl_equal ? result0)) in
      (exist_2 [x1: Z][result2: unit]x1 = result0 result1 tt Post1) in
    (Build_tuple_2 x0 result1) in
  result0.

Definition r1 := (* validation *)
  let (result1, Post1) = (Z_eq_bool `1` `1`) in
  (exist_1 [result2: bool](if result2 then `1 = 1` else `1 <> 1`) result1
  Post1).

Definition r2 := (* validation *)
  let (result1, Post1) = (Z_gt_le_bool `2` `1`) in
  (exist_1 [result2: bool](if result2 then `2 > 1` else `2 <= 1`) result1
  Post1).

Definition r3 := (* validation *)
  let (result1, Post1) = (Z_ge_lt_bool `2` `1`) in
  (exist_1 [result2: bool](if result2 then `2 >= 1` else `2 < 1`) result1
  Post1).

Definition r4 := (* validation *)
  let (result1, Post1) = (Z_lt_ge_bool `1` `2`) in
  (exist_1 [result2: bool](if result2 then `1 < 2` else `1 >= 2`) result1
  Post1).

Definition r5 := (* validation *)
  let (result1, Post1) = (Z_le_gt_bool `1` `2`) in
  (exist_1 [result2: bool](if result2 then `1 <= 2` else `1 > 2`) result1
  Post1).

Definition r6 := (* validation *)
  let (result1, Post1) = (Z_noteq_bool `1` `2`) in
  (exist_1 [result2: bool](if result2 then `1 <> 2` else `1 = 2`) result1
  Post1).

Definition r7 := (* validation *)
  let (result, Bool1) =
    let (result1, Post1) = (Z_eq_bool `1` `2`) in
    (exist_1 [result2: bool](if result2 then `1 = 2` else `1 <> 2`) result1
    Post1) in
  (Cases (btest [result:bool](if result then `1 = 2` else `1 <> 2`) result
          Bool1) of
  | (left Test2) => true
  | (right Test1) =>
      let (result0, Post2) =
        let (result2, Post3) = (Z_eq_bool `2` `3`) in
        (exist_1 [result3: bool]
        (if result3 then `2 = 3` else `2 <> 3`) result2 Post3) in
      result0 end).

Definition r8 := (* validation *)
  let (result, Bool1) =
    let (result1, Post1) = (Z_eq_bool `1` `2`) in
    (exist_1 [result2: bool](if result2 then `1 = 2` else `1 <> 2`) result1
    Post1) in
  (Cases (btest [result:bool](if result then `1 = 2` else `1 <> 2`) result
          Bool1) of
  | (left Test2) =>
      let (result0, Post2) =
        let (result2, Post3) = (Z_eq_bool `2` `3`) in
        (exist_1 [result3: bool]
        (if result3 then `2 = 3` else `2 <> 3`) result2 Post3) in
      result0
  | (right Test1) => false end).

Lemma arr1_po_1 : 
  `0 <= 0` /\ `0 < 10`.
Proof. (* arr1_po_1 *)
Omega.
Save.




Definition arr1 := (* validation *)
  [v6: (array `10` Z)]let Pre1 = arr1_po_1 in
                      (access v6 `0`).

Lemma arr2_po_1 : 
  `0 <= 1 + 2` /\ `1 + 2 < 10`.
Proof. (* arr2_po_1 *)
Omega.
Save.




Definition arr2 := (* validation *)
  [v6: (array `10` Z)]let Pre1 = arr2_po_1 in
                      (access v6 `1 + 2`).

Lemma arr3_po_1 : 
  (v4: Z)
  (Pre2: `v4 = 0`)
  `0 <= v4` /\ `v4 < 10`.
Proof. (* arr3_po_1 *)
Intros; Omega.
Save.




Definition arr3 := (* validation *)
  [v4: Z; v6: (array `10` Z); Pre2: `v4 = 0`]
    let Pre1 = (arr3_po_1 v4 Pre2) in
    (access v6 v4).

Lemma arr4_po_1 : 
  (v6: (array `10` Z))
  (Pre3: `(access v6 0) = 9`)
  `0 <= 0` /\ `0 < 10`.
Proof. (* arr4_po_1 *)
Intros; Omega.
Save.

Lemma arr4_po_2 : 
  (v6: (array `10` Z))
  (Pre3: `(access v6 0) = 9`)
  (Pre2: `0 <= 0` /\ `0 < 10`)
  `0 <= (access v6 0)` /\ `(access v6 0) < 10`.
Proof. (* arr4_po_2 *)
Intros; Omega.
Save.




Definition arr4 := (* validation *)
  [v6: (array `10` Z); Pre3: `(access v6 0) = 9`]
    let Pre2 = (arr4_po_1 v6 Pre3) in
    let Pre1 = (arr4_po_2 v6 Pre3 Pre2) in
    (access v6 (access v6 `0`)).

Lemma arr5_po_1 : 
  (v6: (array `10` Z))
  (result: Z)
  (Post1: (store v6 `0` result) = (store v6 `0` `1`))
  `0 <= 0` /\ `0 < 10`.
Proof. (* arr5_po_1 *)
Intros; Omega.
Save.




Definition arr5 := (* validation *)
  [v6: (array `10` Z)]
    let (result, Post1) = (exist_1 [result: Z]
      (store v6 `0` result) = (store v6 `0` `1`) `1`
      (refl_equal ? (store v6 `0` `1`))) in
    let Pre1 = (arr5_po_1 v6 result Post1) in
    (exist_2 [v10: (array `10` Z)][result1: unit]
    v10 = (store v6 `0` `1`) (store v6 `0` result) tt Post1).

Lemma arr6_po_1 : 
  (v6: (array `10` Z))
  (result: Z)
  (Post1: (store v6 `1 + 2` result) = (store v6 `1 + 2` `3 + 4`))
  `0 <= 1 + 2` /\ `1 + 2 < 10`.
Proof. (* arr6_po_1 *)
Intros; Omega.
Save.




Definition arr6 := (* validation *)
  [v6: (array `10` Z)]
    let (result, Post1) = (exist_1 [result: Z]
      (store v6 `1 + 2` result) = (store v6 `1 + 2` `3 + 4`) `3 + 4`
      (refl_equal ? (store v6 `1 + 2` `3 + 4`))) in
    let Pre1 = (arr6_po_1 v6 result Post1) in
    (exist_2 [v10: (array `10` Z)][result1: unit]
    v10 = (store v6 `1 + 2` `3 + 4`) (store v6 `1 + 2` result) tt Post1).

Lemma arr7_po_1 : 
  (v6: (array `10` Z))
  (Pre3: `(access v6 0) = 9`)
  `0 <= 0` /\ `0 < 10`.
Proof. (* arr7_po_1 *)
Intros; Omega.
Save.

Lemma arr7_po_2 : 
  (v6: (array `10` Z))
  (Pre3: `(access v6 0) = 9`)
  (Pre2: `0 <= 0` /\ `0 < 10`)
  (result: Z)
  (Post1: (store v6 (access v6 `0`) result) = (store v6 (access v6 `0`) `1`))
  `0 <= (access v6 0)` /\ `(access v6 0) < 10`.
Proof. (* arr7_po_2 *)
Intros; Omega.
Save.










Definition arr7 := (* validation *)
  [v6: (array `10` Z); Pre3: `(access v6 0) = 9`]
    let Pre2 = (arr7_po_1 v6 Pre3) in
    let (result, Post1) = (exist_1 [result: Z]
      (store v6 (access v6 `0`) result) = (store v6 (access v6 `0`) `1`) 
      `1` (refl_equal ? (store v6 (access v6 `0`) `1`))) in
    let Pre1 = (arr7_po_2 v6 Pre3 Pre2 result Post1) in
    (exist_2 [v10: (array `10` Z)][result1: unit]
    v10 = (store v6 (access v6 `0`) `1`) (store v6 (access v6 `0`) result) 
    tt Post1).

Definition fc1 := (* validation *)
  (f5 v5).

Definition fc2 := (* validation *)
  (f4 tt).

Lemma fc3_po_1 : 
  (result: Z)
  (Post2: result = `0`)
  (result0: Z)
  (Post1: result0 = `0`)
  `result >= 0`.
Proof. Intros; Omega. Save.







Definition fc3 := (* validation *)
  let (result, Post2) = (exist_1 [result: Z]result = `0` `0`
    (refl_equal ? `0`)) in
  let result0 =
    let (result0, Post1) = (exist_1 [result0: Z]result0 = `0` `0`
      (refl_equal ? `0`)) in
    let Pre3 = (fc3_po_1 result Post2 result0 Post1) in
    let (b0, result1, Post3) =
      let Pre1 = Pre3 in
      let Pre2 = Pre1 in
      let (b0, r, Post4) = let Pre4 = Pre2 in
                           (f3 result result0 Pre4) in
      (exist_2 [b1: Z][result2: Z]`b1 = result0 + result + result2` b0 
      r Post4) in
    result1 in
  result0.

Definition an1 := (* validation *)
  (exist_1 [result: Z]`result = 0` `0` (refl_equal ? `0`)).

Lemma an2_po_1 : 
  (v4: Z)
  (Pre1: `v4 >= 0`)
  (v9: Z)
  (Post1: v9 = `v4 + 1`)
  `v9 > v4`.
Proof.
Intros; Omega.
Save.




Definition an2 := (* validation *)
  [v4: Z; Pre1: `v4 >= 0`]
    let (v9, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `v4 + 1` `v4 + 1`
        (refl_equal ? `v4 + 1`)) in
      (exist_2 [v10: Z][result0: unit]v10 = `v4 + 1` result tt Post1) in
    (exist_2 [v10: Z][result0: unit]`v10 > v4` v9 result
    (an2_po_1 v4 Pre1 v9 Post1)).

Lemma an3_po_1 : 
  (v4: Z)
  (Pre1: `v4 >= 0`)
  (v9: Z)
  (Post1: v9 = `v4 + 1`)
  `v9 > v4`.
Proof.
Intros; Omega.
Save.



(*Why*) Inductive ET_E1 [T:Set] : Set :=
  | Val_E1 : T -> (ET_E1 T)
  | Exn_E1 : (ET_E1 T).

(*Why*) Definition post_E1 :=
  [T:Set][P:Prop][Q:T->Prop][x:(ET_E1 T)]
  Cases x of 
  | (Val_E1 v) => (Q v)
  | Exn_E1 => P
  end.

(*Why*) Implicits post_E1.

(*Why*) Inductive ET_E2 [T:Set] : Set :=
  | Val_E2 : T -> (ET_E2 T)
  | Exn_E2 : Z -> (ET_E2 T).

(*Why*) Definition post_E2 :=
  [T:Set][P:Z -> Prop][Q:T->Prop][x:(ET_E2 T)]
  Cases x of 
  | (Val_E2 v) => (Q v)
  | (Exn_E2 v) => (P v)
  end.

(*Why*) Implicits post_E2.

(*Why*) Inductive ET_E3 [T:Set] : Set :=
  | Val_E3 : T -> (ET_E3 T)
  | Exn_E3 : foo -> (ET_E3 T).

(*Why*) Definition post_E3 :=
  [T:Set][P:foo -> Prop][Q:T->Prop][x:(ET_E3 T)]
  Cases x of 
  | (Val_E3 v) => (Q v)
  | (Exn_E3 v) => (P v)
  end.

(*Why*) Implicits post_E3.


Definition an3 := (* validation *)
  [v4: Z; Pre1: `v4 >= 0`]
    let (v9, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `v4 + 1` `v4 + 1`
        (refl_equal ? `v4 + 1`)) in
      (exist_2 [v10: Z][result0: unit]v10 = `v4 + 1` result tt Post1) in
    (exist_2 [v10: Z][result0: unit]`v10 > v4` v9 result
    (an3_po_1 v4 Pre1 v9 Post1)).

(*Why*) Parameter f1_ex : (n: Z)(EM unit unit).

(*Why*) Parameter f2_ex : (x: Z)(tuple_2 Z (EM unit (EM Z bool))).

