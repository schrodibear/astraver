(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.


(* ----------- PRELIMINAIRES ------------- *)
(* d�finition et propri�t�s de "Maximize"   *)
Require Omega.
Require ZArithRing.

Tactic Definition Omega' := Abstract Omega.

Implicit Arguments On.

(* Induction pour v�rifier qu'on est le maximum *)
Inductive Maximize[t:(array Z); n,m:Z] : Z -> Prop :=
  Maxim_cons : (k:Z)
     (`k <= n` -> (Zle #t[k] m)) ->
     (`k < n` -> (Maximize t n m `k+1`)) -> (Maximize t n m `k`).

(* Signification "extensionnelle" de ce pr�dicat: *)
Lemma Maximize_ext1 : (t:(array Z))(n,m,k,i:Z)
  (Maximize t n m k) -> `k <= i <= n` -> `(access t i) <= m`.
Proof.
  Intros t n m k i H1; Elim H1; Auto.
  Intros k0 H2 H3 HR H4; Case (Z_eq_dec k0 i).
   Intros H; Rewrite <- H; Apply H2; Omega'.
   Intros; Apply HR; Omega'.
Qed.

Lemma Maximize_ext2 : (t:(array Z))(n,m,k:Z)
   ((i:Z)`k <= i <= n` -> `(access t i) <= m`) -> (Maximize t n m k).
Proof.
  Intros t n m k.
     Refine (well_founded_ind ? (Zwf_up n) ?
       [k:Z]((i:Z)`k <= i <= n`->`(access t i) <= m`)->(Maximize t n m k) ? ?).
     Apply Zwf_up_well_founded.
     Clear k; Intros k HR H.
     Constructor 1.
       Intros; Apply H; Omega'.
       Intros; Apply HR.
         Unfold Zwf_up; Omega'.
         Intros; Apply H; Omega'.
Qed.

(* compatibilit� de "Zle" avec "Maximize" *)
Lemma Maximize_Zle: (t:(array Z))(n,m1,m2,k:Z)
  (Maximize t n m1 k) -> `k <= n` -> (Zle m1 m2) -> (Maximize t n m2 k).
Proof.
  Intros t n m1 m2 k H0; Elim H0.
  Intros k0 H1 H2 H3 H4 H5; Constructor 1.
  Omega'. Intros; Apply H3; Omega'.
Qed.

Implicit Arguments Off.
(* ----------- FIN PRELIMINAIRES ----------- *)


(* D�but: preuve de "swap" *)
(* Why obligation from file "maximumsort.mlw", characters 206-210 *)
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
  Intros; Omega.
Save.

(* Why obligation from file "maximumsort.mlw", characters 217-226 *)
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
Intuition ArraySubst t0.
Save.


(* Why obligation from file "maximumsort.mlw", characters 187-233 *)
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
 Intros; Subst t1 t0 v;
 Auto with datatypes.
Save.

Definition swap := (* validation *)
  [i: Z; j: Z; t: (array Z); Pre5: (`0 <= i` /\ `i < (array_length t)`) /\
   `0 <= j` /\ `j < (array_length t)`]
    let Pre4 = (proj1 ? ? Pre5) in
    let (v, Post3) = (exist_1 [result: Z]result = (access t i) (access t i)
      (refl_equal ? (access t i))) in
    let (t0, result, Post4) =
      let Pre2 = Pre4 in
      let Pre3 = (swap_po_1 i j t Pre5 Pre4 v Post3 Pre2) in
      let (t0, result, Post1) = (exist_2 [t1: (array Z)][result1: unit]
        t1 = (store t i (access t j)) (store t i (access t j)) tt
        (refl_equal ? (store t i (access t j)))) in
      let Pre1 = (swap_po_2 i j t Pre5 Pre4 v Post3 Pre2 Pre3 t0 Post1) in
      let (t1, result0, Post2) = (exist_2 [t2: (array Z)][result2: unit]
        t2 = (store t0 j v) (store t0 j v) tt
        (refl_equal ? (store t0 j v))) in
      (exist_2 [t2: (array Z)][result1: unit](exchange t2 t i j) t1 result0
      (swap_po_3 i j t Pre5 Pre4 v Post3 Pre2 Pre3 t0 Post1 Pre1 t1 Post2)) in
    (exist_2 [t1: (array Z)][result0: unit](exchange t1 t i j) t0 result
    Post4).

(* Fin: preuve de "swap" *)


(* D�but: preuve de "maximum" *)
(* Why obligation from file "maximumsort.mlw", characters 602-603 *)
Lemma maximum_po_1 : 
  (n: Z)
  (k: Z)
  (i: Z)
  (t: (array Z))
  (Pre14: (`0 <= k` /\ `k <= i`) /\ `i <= n` /\ `n < (array_length t)` /\
          (Maximize t n (access t i) k))
  (Variant1: Z)
  (n0: Z)
  (k0: Z)
  (i0: Z)
  (Pre13: Variant1 = k0)
  (Pre12: (`0 <= k0` /\ `k0 <= i0`) /\ `i0 <= n0` /\
          `n0 < (array_length t)` /\ (Maximize t n0 (access t i0) k0))
  (Test4: `k0 = 0`)
  (`0 <= i0` /\ `i0 <= n0`) /\ (Maximize t n0 (access t i0) `0`).
Proof.
  Intros; Split.
  Omega'.
  Rewrite Test4 in Pre12; Tauto.
Save.

(* Why obligation from file "maximumsort.mlw", characters 643-647 *)
Lemma maximum_po_2 : 
  (n: Z)
  (k: Z)
  (i: Z)
  (t: (array Z))
  (Pre14: (`0 <= k` /\ `k <= i`) /\ `i <= n` /\ `n < (array_length t)` /\
          (Maximize t n (access t i) k))
  (Variant1: Z)
  (n0: Z)
  (k0: Z)
  (i0: Z)
  (Pre13: Variant1 = k0)
  (Pre12: (`0 <= k0` /\ `k0 <= i0`) /\ `i0 <= n0` /\
          `n0 < (array_length t)` /\ (Maximize t n0 (access t i0) k0))
  (Test3: `k0 <> 0`)
  (nk: Z)
  (Post2: nk = `k0 - 1`)
  `0 <= i0` /\ `i0 < (array_length t)`.
Proof.
   Intros; Omega'.
Save.

(* Why obligation from file "maximumsort.mlw", characters 637-642 *)
Lemma maximum_po_3 : 
  (n: Z)
  (k: Z)
  (i: Z)
  (t: (array Z))
  (Pre14: (`0 <= k` /\ `k <= i`) /\ `i <= n` /\ `n < (array_length t)` /\
          (Maximize t n (access t i) k))
  (Variant1: Z)
  (n0: Z)
  (k0: Z)
  (i0: Z)
  (Pre13: Variant1 = k0)
  (Pre12: (`0 <= k0` /\ `k0 <= i0`) /\ `i0 <= n0` /\
          `n0 < (array_length t)` /\ (Maximize t n0 (access t i0) k0))
  (Test3: `k0 <> 0`)
  (nk: Z)
  (Post2: nk = `k0 - 1`)
  (Pre3: `0 <= i0` /\ `i0 < (array_length t)`)
  `0 <= nk` /\ `nk < (array_length t)`.
Proof.
  Intros; Omega'.
Save.

(* Why obligation from file "maximumsort.mlw", characters 656-675 *)
Lemma maximum_po_4 : 
  (n: Z)
  (k: Z)
  (i: Z)
  (t: (array Z))
  (Pre14: (`0 <= k` /\ `k <= i`) /\ `i <= n` /\ `n < (array_length t)` /\
          (Maximize t n (access t i) k))
  (Variant1: Z)
  (n0: Z)
  (k0: Z)
  (i0: Z)
  (Pre13: Variant1 = k0)
  (Pre12: (`0 <= k0` /\ `k0 <= i0`) /\ `i0 <= n0` /\
          `n0 < (array_length t)` /\ (Maximize t n0 (access t i0) k0))
  (Test3: `k0 <> 0`)
  (nk: Z)
  (Post2: nk = `k0 - 1`)
  (Test2: `(access t nk) > (access t i0)`)
  (`0 <= nk` /\ `nk <= nk`) /\ `nk <= n0` /\ `n0 < (array_length t)` /\
  (Maximize t n0 (access t nk) nk).
Proof.
Repeat (Split; [Omega' | Auto]).
Subst nk.
Ring `k0-1+1`; Intros;
 Apply Maximize_Zle with m1:=(access t i0); Omega' Orelse Tauto.
Save.

(* Why obligation from file "maximumsort.mlw", characters 503-756 *)
Lemma maximum_po_5 : 
  (n: Z)
  (k: Z)
  (i: Z)
  (t: (array Z))
  (Pre14: (`0 <= k` /\ `k <= i`) /\ `i <= n` /\ `n < (array_length t)` /\
          (Maximize t n (access t i) k))
  (Variant1: Z)
  (n0: Z)
  (k0: Z)
  (i0: Z)
  (Pre13: Variant1 = k0)
  (Pre12: (`0 <= k0` /\ `k0 <= i0`) /\ `i0 <= n0` /\
          `n0 < (array_length t)` /\ (Maximize t n0 (access t i0) k0))
  (Test3: `k0 <> 0`)
  (nk: Z)
  (Post2: nk = `k0 - 1`)
  (Test2: `(access t nk) > (access t i0)`)
  (Pre11: (`0 <= nk` /\ `nk <= nk`) /\ `nk <= n0` /\
          `n0 < (array_length t)` /\ (Maximize t n0 (access t nk) nk))
  (Pre9: (`0 <= nk` /\ `nk <= nk`) /\ `nk <= n0` /\
         `n0 < (array_length t)` /\ (Maximize t n0 (access t nk) nk))
  (Pre10: (`0 <= nk` /\ `nk <= nk`) /\ `nk <= n0` /\
          `n0 < (array_length t)` /\ (Maximize t n0 (access t nk) nk))
  (Zwf `0` nk Variant1).
Proof.
  Intros; Subst nk;
  Unfold Zwf; Omega'.  
Save.

(* Why obligation from file "maximumsort.mlw", characters 684-702 *)
Lemma maximum_po_6 : 
  (n: Z)
  (k: Z)
  (i: Z)
  (t: (array Z))
  (Pre14: (`0 <= k` /\ `k <= i`) /\ `i <= n` /\ `n < (array_length t)` /\
          (Maximize t n (access t i) k))
  (Variant1: Z)
  (n0: Z)
  (k0: Z)
  (i0: Z)
  (Pre13: Variant1 = k0)
  (Pre12: (`0 <= k0` /\ `k0 <= i0`) /\ `i0 <= n0` /\
          `n0 < (array_length t)` /\ (Maximize t n0 (access t i0) k0))
  (Test3: `k0 <> 0`)
  (nk: Z)
  (Post2: nk = `k0 - 1`)
  (Test1: `(access t nk) <= (access t i0)`)
  (`0 <= nk` /\ `nk <= i0`) /\ `i0 <= n0` /\ `n0 < (array_length t)` /\
  (Maximize t n0 (access t i0) nk).
Proof.
  Intros; Subst nk.
  Repeat (Split; [Omega' | Auto]); Ring `k0-1+1`; Tauto.
Save.

(* Why obligation from file "maximumsort.mlw", characters 503-756 *)
Lemma maximum_po_7 : 
  (n: Z)
  (k: Z)
  (i: Z)
  (t: (array Z))
  (Pre14: (`0 <= k` /\ `k <= i`) /\ `i <= n` /\ `n < (array_length t)` /\
          (Maximize t n (access t i) k))
  (Variant1: Z)
  (n0: Z)
  (k0: Z)
  (i0: Z)
  (Pre13: Variant1 = k0)
  (Pre12: (`0 <= k0` /\ `k0 <= i0`) /\ `i0 <= n0` /\
          `n0 < (array_length t)` /\ (Maximize t n0 (access t i0) k0))
  (Test3: `k0 <> 0`)
  (nk: Z)
  (Post2: nk = `k0 - 1`)
  (Test1: `(access t nk) <= (access t i0)`)
  (Pre7: (`0 <= nk` /\ `nk <= i0`) /\ `i0 <= n0` /\
         `n0 < (array_length t)` /\ (Maximize t n0 (access t i0) nk))
  (Pre5: (`0 <= nk` /\ `nk <= i0`) /\ `i0 <= n0` /\
         `n0 < (array_length t)` /\ (Maximize t n0 (access t i0) nk))
  (Pre6: (`0 <= nk` /\ `nk <= i0`) /\ `i0 <= n0` /\
         `n0 < (array_length t)` /\ (Maximize t n0 (access t i0) nk))
  (Zwf `0` nk Variant1).
Proof.
  Intros; Subst nk.
  Unfold Zwf; Omega'.  
Save.

Definition maximum := (* validation *)
  [n: Z; k: Z; i: Z; t: (array Z); Pre14: (`0 <= k` /\ `k <= i`) /\
   `i <= n` /\ `n < (array_length t)` /\ (Maximize t n (access t i) k)]
    (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`) [Variant1: Z]
      (n0: Z)(k0: Z)(i0: Z)(_: Variant1 = k0)(_0: (`0 <= k0` /\
      `k0 <= i0`) /\ `i0 <= n0` /\ `n0 < (array_length t)` /\
      (Maximize t n0 (access t i0) k0))
      (sig_1 Z [result: Z]((`0 <= result` /\ `result <= n0`) /\
       (Maximize t n0 (access t result) `0`)))
      [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
       (n0: Z)(k0: Z)(i0: Z)(_: Variant2 = k0)(_0: (`0 <= k0` /\
       `k0 <= i0`) /\ `i0 <= n0` /\ `n0 < (array_length t)` /\
       (Maximize t n0 (access t i0) k0))
       (sig_1 Z [result: Z]((`0 <= result` /\ `result <= n0`) /\
        (Maximize t n0 (access t result) `0`)));
       n0: Z; k0: Z; i0: Z; Pre13: Variant1 = k0; Pre12: (`0 <= k0` /\
       `k0 <= i0`) /\ `i0 <= n0` /\ `n0 < (array_length t)` /\
       (Maximize t n0 (access t i0) k0)]
        let (result, Bool4) =
          let (result1, Post5) = (Z_eq_bool k0 `0`) in
          (exist_1 [result2: bool]
          (if result2 then `k0 = 0` else `k0 <> 0`) result1 Post5) in
        (Cases (btest [result:bool](if result then `k0 = 0` else `k0 <> 0`)
                result Bool4) of
        | (left Test4) =>
            let (result0, Post13) = (exist_1 [result0: Z](`0 <= result0` /\
              `result0 <= n0`) /\ (Maximize t n0 (access t result0) `0`) 
              i0
              (maximum_po_1 n k i t Pre14 Variant1 n0 k0 i0 Pre13 Pre12
              Test4)) in
            (exist_1 [result1: Z](`0 <= result1` /\ `result1 <= n0`) /\
            (Maximize t n0 (access t result1) `0`) result0 Post13)
        | (right Test3) =>
            let (result0, Post6) =
              let (nk, Post2) = (exist_1 [result0: Z]
                result0 = `k0 - 1` `k0 - 1` (refl_equal ? `k0 - 1`)) in
              let (result0, Post7) =
                let (result0, Bool3) =
                  let Pre3 =
                    (maximum_po_2 n k i t Pre14 Variant1 n0 k0 i0 Pre13 Pre12
                    Test3 nk Post2) in
                  let result1 =
                    let Pre2 =
                      (maximum_po_3 n k i t Pre14 Variant1 n0 k0 i0 Pre13
                      Pre12 Test3 nk Post2 Pre3) in
                    (Z_gt_le_bool (access t nk)) in
                  let (result2, Post8) = (result1 (access t i0)) in
                  (exist_1 [result3: bool]
                  (if result3 then `(access t nk) > (access t i0)`
                   else `(access t nk) <= (access t i0)`) result2
                  Post8) in
                (Cases (btest
                        [result0:bool](if result0
                                       then `(access t nk) > (access t i0)`
                                       else `(access t nk) <= (access t i0)`)
                        result0 Bool3) of
                | (left Test2) =>
                    let Pre11 =
                      (maximum_po_4 n k i t Pre14 Variant1 n0 k0 i0 Pre13
                      Pre12 Test3 nk Post2 Test2) in
                    let (result1, Post11) =
                      let Pre9 = Pre11 in
                      let Pre10 = Pre9 in
                      let (result3, Post12) =
                        ((wf1 nk)
                          (maximum_po_5 n k i t Pre14 Variant1 n0 k0 i0 Pre13
                          Pre12 Test3 nk Post2 Test2 Pre11 Pre9 Pre10) 
                          n0 nk nk (refl_equal ? nk) Pre10) in
                      (exist_1 [result4: Z](`0 <= result4` /\
                      `result4 <= n0`) /\
                      (Maximize t n0 (access t result4) `0`) result3 Post12) in
                    (exist_1 [result2: Z](`0 <= result2` /\
                    `result2 <= n0`) /\
                    (Maximize t n0 (access t result2) `0`) result1 Post11)
                | (right Test1) =>
                    let Pre7 =
                      (maximum_po_6 n k i t Pre14 Variant1 n0 k0 i0 Pre13
                      Pre12 Test3 nk Post2 Test1) in
                    let (result1, Post9) =
                      let Pre5 = Pre7 in
                      let Pre6 = Pre5 in
                      let (result3, Post10) =
                        ((wf1 nk)
                          (maximum_po_7 n k i t Pre14 Variant1 n0 k0 i0 Pre13
                          Pre12 Test3 nk Post2 Test1 Pre7 Pre5 Pre6) 
                          n0 nk i0 (refl_equal ? nk) Pre6) in
                      (exist_1 [result4: Z](`0 <= result4` /\
                      `result4 <= n0`) /\
                      (Maximize t n0 (access t result4) `0`) result3 Post10) in
                    (exist_1 [result2: Z](`0 <= result2` /\
                    `result2 <= n0`) /\
                    (Maximize t n0 (access t result2) `0`) result1 Post9) end) in
              (exist_1 [result1: Z](`0 <= result1` /\ `result1 <= n0`) /\
              (Maximize t n0 (access t result1) `0`) result0 Post7) in
            (exist_1 [result1: Z](`0 <= result1` /\ `result1 <= n0`) /\
            (Maximize t n0 (access t result1) `0`) result0 Post6) end) 
      k n k i (refl_equal ? k) Pre14).

(* fin preuve de maximum *)

(* Why obligation from file "maximumsort.mlw", characters 1124-1144 *)
Lemma maxisort_po_1 : 
  (t: (array Z))
  (Pre10: `0 <= (array_length t)`)
  (result: Z)
  (Post3: result = `(array_length t) - 1`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array Z))
  (Pre9: Variant1 = `i0 + 1`)
  (Pre8: (`0 <= i0 + 1` /\ `i0 + 1 <= (array_length t0)`) /\
         (sorted_array t0 `i0 + 1` `(array_length t0) - 1`) /\
         (permut t0 t) /\
         ((`i0 + 1 < (array_length t0)` ->
           (Maximize t0 i0 (access t0 `i0 + 1`) `0`))))
  (Test2: `i0 >= 0`)
  (`0 <= i0` /\ `i0 <= i0`) /\ `i0 <= i0` /\ `i0 < (array_length t0)` /\
  (Maximize t0 i0 (access t0 i0) i0).
Proof.
  Intros; Split. Omega'. Split. Omega'. Split. Omega'.
  Constructor 1. Omega'.
  Intros H; Absurd `i0 < i0`; Omega'.
Save.

(* Why obligation from file "maximumsort.mlw", characters 1156-1169 *)
Lemma maxisort_po_2 : 
  (t: (array Z))
  (Pre10: `0 <= (array_length t)`)
  (result: Z)
  (Post3: result = `(array_length t) - 1`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array Z))
  (Pre9: Variant1 = `i0 + 1`)
  (Pre8: (`0 <= i0 + 1` /\ `i0 + 1 <= (array_length t0)`) /\
         (sorted_array t0 `i0 + 1` `(array_length t0) - 1`) /\
         (permut t0 t) /\
         ((`i0 + 1 < (array_length t0)` ->
           (Maximize t0 i0 (access t0 `i0 + 1`) `0`))))
  (Test2: `i0 >= 0`)
  (Pre7: (`0 <= i0` /\ `i0 <= i0`) /\ `i0 <= i0` /\
         `i0 < (array_length t0)` /\ (Maximize t0 i0 (access t0 i0) i0))
  (r: Z)
  (Post7: (`0 <= r` /\ `r <= i0`) /\ (Maximize t0 i0 (access t0 r) `0`))
  (`0 <= i0` /\ `i0 < (array_length t0)`) /\ `0 <= r` /\
  `r < (array_length t0)`.
Proof.
  Intros;  Omega'.
Save.

(* Why obligation from file "maximumsort.mlw", characters 1115-1170 *)
Lemma maxisort_po_3 : 
  (t: (array Z))
  (Pre10: `0 <= (array_length t)`)
  (result: Z)
  (Post3: result = `(array_length t) - 1`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array Z))
  (Pre9: Variant1 = `i0 + 1`)
  (Pre8: (`0 <= i0 + 1` /\ `i0 + 1 <= (array_length t0)`) /\
         (sorted_array t0 `i0 + 1` `(array_length t0) - 1`) /\
         (permut t0 t) /\
         ((`i0 + 1 < (array_length t0)` ->
           (Maximize t0 i0 (access t0 `i0 + 1`) `0`))))
  (Test2: `i0 >= 0`)
  (Pre7: (`0 <= i0` /\ `i0 <= i0`) /\ `i0 <= i0` /\
         `i0 < (array_length t0)` /\ (Maximize t0 i0 (access t0 i0) i0))
  (r: Z)
  (Post7: (`0 <= r` /\ `r <= i0`) /\ (Maximize t0 i0 (access t0 r) `0`))
  (Pre6: (`0 <= i0` /\ `i0 < (array_length t0)`) /\ `0 <= r` /\
         `r < (array_length t0)`)
  (t1: (array Z))
  (Post9: (exchange t1 t0 i0 r))
  ((i:Z)
   (i = `i0 - 1` -> ((`0 <= i + 1` /\ `i + 1 <= (array_length t1)`) /\
    (sorted_array t1 `i + 1` `(array_length t1) - 1`) /\ (permut t1 t) /\
    ((`i + 1 < (array_length t1)` -> (Maximize t1 i (access t1 `i + 1`) `0`)))) /\
    (Zwf `0` `i + 1` `i0 + 1`))).
Proof.
 Intros; Decompose [and] Pre8; Clear Pre8; Split.
   ArrayLength.
   Split.
   Omega.
   Split.
   (* post-condition 1 *)
   Unfold sorted_array in H0;  Unfold sorted_array.
   Intros C1 k C2 C3;
   Case Post9.
    Intros Clength C4 C5 C6 C7 C8.
     Case (Z_eq_dec k i0).
       Intros C9; Rewrite C9; Rewrite C6; Rewrite C8; Try Omega'.
       Apply Maximize_ext1 with n:=i0 k:=`0`; Try Omega'.
         Apply H5; Omega'.
       Intros C9; Rewrite C8; Try Omega'. Rewrite C8; Try Omega'.
       Apply H0; Try Omega'.
   (* post-condition 2 *)
   Split. Apply permut_trans with t':=t0; Auto.
   EApply exchange_is_permut; EAuto.
   (* post-condition 3 *)
   Decompose [and] Post7; Clear Post7. Case Post9; Clear Post9.
   Intros Clength C1 C2 C3 C4 C5 C5a; Replace `i+1` with i0. Rewrite C3.
     Apply Maximize_ext2; Intros i' C6.
     Case (Z_eq_dec i' r).
       Intros C7; Rewrite C7; Rewrite C4.
         Apply Maximize_ext1 with n:=i0 k:=`0`; Try Omega'; Auto.
       Intros; Rewrite C5; Try Omega'.
         Apply Maximize_ext1 with n:=i0 k:=`0`; Try Omega'; Auto.
   Omega.
   Unfold Zwf; Omega.
Save.

(* Why obligation from file "maximumsort.mlw", characters 876-1194 *)
Lemma maxisort_po_4 : 
  (t: (array Z))
  (Pre10: `0 <= (array_length t)`)
  (result: Z)
  (Post3: result = `(array_length t) - 1`)
  (Variant1: Z)
  (i0: Z)
  (t0: (array Z))
  (Pre9: Variant1 = `i0 + 1`)
  (Pre8: (`0 <= i0 + 1` /\ `i0 + 1 <= (array_length t0)`) /\
         (sorted_array t0 `i0 + 1` `(array_length t0) - 1`) /\
         (permut t0 t) /\
         ((`i0 + 1 < (array_length t0)` ->
           (Maximize t0 i0 (access t0 `i0 + 1`) `0`))))
  (Test2: `i0 >= 0`)
  (t1: (array Z))
  (Post6: ((i:Z)
           (i = `i0 - 1` -> ((`0 <= i + 1` /\
            `i + 1 <= (array_length t1)`) /\
            (sorted_array t1 `i + 1` `(array_length t1) - 1`) /\
            (permut t1 t) /\
            ((`i + 1 < (array_length t1)` ->
              (Maximize t1 i (access t1 `i + 1`) `0`)))) /\
            (Zwf `0` `i + 1` `i0 + 1`))))
  (i1: Z)
  (Post1: i1 = `i0 - 1`)
  ((`0 <= i1 + 1` /\ `i1 + 1 <= (array_length t1)`) /\
  (sorted_array t1 `i1 + 1` `(array_length t1) - 1`) /\ (permut t1 t) /\
  ((`i1 + 1 < (array_length t1)` -> (Maximize t1 i1 (access t1 `i1 + 1`) `0`)))) /\
  (Zwf `0` `i1 + 1` `i0 + 1`).
Proof.
Intuition.
Save.

(* Why obligation from file "maximumsort.mlw", characters 911-1086 *)
Lemma maxisort_po_5 : 
  (t: (array Z))
  (Pre10: `0 <= (array_length t)`)
  (result: Z)
  (Post3: result = `(array_length t) - 1`)
  (`0 <= result + 1` /\ `result + 1 <= (array_length t)`) /\
  (sorted_array t `result + 1` `(array_length t) - 1`) /\ (permut t t) /\
  ((`result + 1 < (array_length t)` ->
    (Maximize t result (access t `result + 1`) `0`))).
Proof.
  Intros;  Subst result; Ring `(array_length t)-1+1`; Split.   Omega'.
  Split. Unfold sorted_array; Intros H; 
  Absurd `(array_length t) <= (array_length t)-1`; [Omega' | Auto].
  Split. Apply permut_refl.
  Intros H; Absurd `(array_length t) < (array_length t)`; [Omega' | Auto].
Save.

(* Why obligation from file "maximumsort.mlw", characters 808-1254 *)
Lemma maxisort_po_6 : 
  (t: (array Z))
  (Pre10: `0 <= (array_length t)`)
  (result: Z)
  (Post3: result = `(array_length t) - 1`)
  (i0: Z)
  (t0: (array Z))
  (Post2: ((`0 <= i0 + 1` /\ `i0 + 1 <= (array_length t0)`) /\
          (sorted_array t0 `i0 + 1` `(array_length t0) - 1`) /\
          (permut t0 t) /\
          ((`i0 + 1 < (array_length t0)` ->
            (Maximize t0 i0 (access t0 `i0 + 1`) `0`)))) /\
          `i0 < 0`)
  (sorted_array t0 `0` `(array_length t0) - 1`) /\ (permut t0 t).
Proof.
  Intros; Cut `i0+1=0`; [Intros H; Rewrite H in Post2; Split; Tauto | Omega'].
Save.

Definition maxisort := (* validation *)
  [t: (array Z); Pre10: `0 <= (array_length t)`]
    let (result, Post3) = (exist_1 [result: Z]
      result = `(array_length t) - 1` `(array_length t) - 1`
      (refl_equal ? `(array_length t) - 1`)) in
    let (i0, t0, result0, Post2) =
      (well_founded_induction Z (Zwf ZERO) (Zwf_well_founded `0`)
        [Variant1: Z](i0: Z)(t0: (array Z))(_: Variant1 = `i0 + 1`)
        (_0: (`0 <= i0 + 1` /\ `i0 + 1 <= (array_length t0)`) /\
        (sorted_array t0 `i0 + 1` `(array_length t0) - 1`) /\
        (permut t0 t) /\
        ((`i0 + 1 < (array_length t0)` ->
          (Maximize t0 i0 (access t0 `i0 + 1`) `0`))))
        (sig_3 Z (array Z) unit [i1: Z][t1: (array Z)][result0: unit]
         (((`0 <= i1 + 1` /\ `i1 + 1 <= (array_length t1)`) /\
         (sorted_array t1 `i1 + 1` `(array_length t1) - 1`) /\
         (permut t1 t) /\
         ((`i1 + 1 < (array_length t1)` ->
           (Maximize t1 i1 (access t1 `i1 + 1`) `0`)))) /\
         `i1 < 0`))
        [Variant1: Z; wf1: (Variant2: Z)(Pre1: (Zwf `0` Variant2 Variant1))
         (i0: Z)(t0: (array Z))(_: Variant2 = `i0 + 1`)(_0: (`0 <= i0 + 1` /\
         `i0 + 1 <= (array_length t0)`) /\
         (sorted_array t0 `i0 + 1` `(array_length t0) - 1`) /\
         (permut t0 t) /\
         ((`i0 + 1 < (array_length t0)` ->
           (Maximize t0 i0 (access t0 `i0 + 1`) `0`))))
         (sig_3 Z (array Z) unit [i1: Z][t1: (array Z)][result0: unit]
          (((`0 <= i1 + 1` /\ `i1 + 1 <= (array_length t1)`) /\
          (sorted_array t1 `i1 + 1` `(array_length t1) - 1`) /\
          (permut t1 t) /\
          ((`i1 + 1 < (array_length t1)` ->
            (Maximize t1 i1 (access t1 `i1 + 1`) `0`)))) /\
          `i1 < 0`));
         i0: Z; t0: (array Z); Pre9: Variant1 = `i0 + 1`;
         Pre8: (`0 <= i0 + 1` /\ `i0 + 1 <= (array_length t0)`) /\
         (sorted_array t0 `i0 + 1` `(array_length t0) - 1`) /\
         (permut t0 t) /\
         ((`i0 + 1 < (array_length t0)` ->
           (Maximize t0 i0 (access t0 `i0 + 1`) `0`)))]
          let (result0, Bool1) =
            let (result2, Post5) = (Z_ge_lt_bool i0 `0`) in
            (exist_1 [result3: bool]
            (if result3 then `i0 >= 0` else `i0 < 0`) result2 Post5) in
          (Cases (btest
                  [result0:bool](if result0 then `i0 >= 0` else `i0 < 0`)
                  result0 Bool1) of
          | (left Test2) =>
              let (i1, t1, result1, Post2) =
                let (i1, t1, result1, Post4) =
                  let (t1, result1, Post6) =
                    let Pre7 =
                      (maxisort_po_1 t Pre10 result Post3 Variant1 i0 t0 Pre9
                      Pre8 Test2) in
                    let (r, Post7) =
                      let Pre2 = Pre7 in
                      let Pre3 = Pre2 in
                      let (result3, Post8) = (maximum i0 i0 i0 t0 Pre2) in
                      (exist_1 [result4: Z](`0 <= result4` /\
                      `result4 <= i0`) /\
                      (Maximize t0 i0 (access t0 result4) `0`) result3 Post8) in
                    let Pre6 =
                      (maxisort_po_2 t Pre10 result Post3 Variant1 i0 t0 Pre9
                      Pre8 Test2 Pre7 r Post7) in
                    let (t1, result1, Post9) =
                      let Pre4 = Pre6 in
                      let Pre5 = Pre4 in
                      let (t1, result3, Post10) = (swap i0 r t0 Pre4) in
                      (exist_2 [t2: (array Z)][result4: unit]
                      (exchange t2 t0 i0 r) t1 result3 Post10) in
                    (exist_2 [t2: (array Z)][result2: unit]
                    ((i:Z)
                     (i = `i0 - 1` -> ((`0 <= i + 1` /\
                      `i + 1 <= (array_length t2)`) /\
                      (sorted_array t2 `i + 1` `(array_length t2) - 1`) /\
                      (permut t2 t) /\
                      ((`i + 1 < (array_length t2)` ->
                        (Maximize t2 i (access t2 `i + 1`) `0`)))) /\
                      (Zwf `0` `i + 1` `i0 + 1`))) t1
                    result1
                    (maxisort_po_3 t Pre10 result Post3 Variant1 i0 t0 Pre9
                    Pre8 Test2 Pre7 r Post7 Pre6 t1 Post9)) in
                  let (i1, result2, Post1) =
                    let (result2, Post1) = (exist_1 [result2: Z]
                      result2 = `i0 - 1` `i0 - 1` (refl_equal ? `i0 - 1`)) in
                    (exist_2 [i2: Z][result3: unit]i2 = `i0 - 1` result2 
                    tt Post1) in
                  (exist_3 [i2: Z][t2: (array Z)][result3: unit]
                  ((`0 <= i2 + 1` /\ `i2 + 1 <= (array_length t2)`) /\
                  (sorted_array t2 `i2 + 1` `(array_length t2) - 1`) /\
                  (permut t2 t) /\
                  ((`i2 + 1 < (array_length t2)` ->
                    (Maximize t2 i2 (access t2 `i2 + 1`) `0`)))) /\
                  (Zwf `0` `i2 + 1` `i0 + 1`) i1 t1 result2
                  (maxisort_po_4 t Pre10 result Post3 Variant1 i0 t0 Pre9
                  Pre8 Test2 t1 Post6 i1 Post1)) in
                ((wf1 `i1 + 1`) (loop_variant_1 Pre9 Post4) i1 t1
                  (refl_equal ? `i1 + 1`) (proj1 ? ? Post4)) in
              (exist_3 [i2: Z][t2: (array Z)][result2: unit]
              ((`0 <= i2 + 1` /\ `i2 + 1 <= (array_length t2)`) /\
              (sorted_array t2 `i2 + 1` `(array_length t2) - 1`) /\
              (permut t2 t) /\
              ((`i2 + 1 < (array_length t2)` ->
                (Maximize t2 i2 (access t2 `i2 + 1`) `0`)))) /\
              `i2 < 0` i1 t1 result1 Post2)
          | (right Test1) =>
              let (i1, t1, result1, Post2) = (exist_3 [i1: Z][t1: (array Z)]
                [result1: unit]((`0 <= i1 + 1` /\
                `i1 + 1 <= (array_length t1)`) /\
                (sorted_array t1 `i1 + 1` `(array_length t1) - 1`) /\
                (permut t1 t) /\
                ((`i1 + 1 < (array_length t1)` ->
                  (Maximize t1 i1 (access t1 `i1 + 1`) `0`)))) /\ `i1 < 0` 
                i0 t0 tt (conj ? ? Pre8 Test1)) in
              (exist_3 [i2: Z][t2: (array Z)][result2: unit]
              ((`0 <= i2 + 1` /\ `i2 + 1 <= (array_length t2)`) /\
              (sorted_array t2 `i2 + 1` `(array_length t2) - 1`) /\
              (permut t2 t) /\
              ((`i2 + 1 < (array_length t2)` ->
                (Maximize t2 i2 (access t2 `i2 + 1`) `0`)))) /\
              `i2 < 0` i1 t1 result1 Post2) end) `result + 1` result 
        t (refl_equal ? `result + 1`) (maxisort_po_5 t Pre10 result Post3)) in
    (exist_2 [t1: (array Z)][result1: unit]
    (sorted_array t1 `0` `(array_length t1) - 1`) /\ (permut t1 t) t0 
    result0 (maxisort_po_6 t Pre10 result Post3 i0 t0 Post2)).

