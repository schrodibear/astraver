(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

Definition p1 := (* validation *)
  (exist_1 (qcomb [result: unit]True [result: unit]False) (Exn unit tt) I).

Definition p2 := (* validation *)
  let (result, Post1) = (exist_1 [result: Z]`result = 1` `1`
    (refl_equal ? `1`)) in
  (exist_1 (qcomb [result0: Z]`result0 = 1` [result0: unit]False) (Exn unit
                                                                    result)
  Post1).

Definition p2a := (* validation *)
  let (result, Post1) =
    (exist_1 (qcomb [result: unit]True [result: Z]False) (Exn Z tt) I) in
  Cases (decomp1 Post1) of
  | (Qval (exist result Post2)) =>
    (exist_1 (qcomb [result0: unit]True
              (qcomb [result0: Z]False [result0: unit]False)) (Val unit
                                                                (Exn unit
                                                                  result))
    Post2)
  | (Qexn _ Post3) =>
    (exist_1 (qcomb [result0: unit]True
              (qcomb [result0: Z]False [result0: unit]False)) (Exn
                                                                (EM Z unit)
                                                                tt) I)
  end.

Definition p3 := (* validation *)
  let (result, Post1) =
    let (result, Post2) = (exist_1 [result: Z]`result = 1` `1`
      (refl_equal ? `1`)) in
    (exist_1 (qcomb [result0: Z]`result0 = 1` [result0: unit]`2 = 1`) 
    (Exn unit result) Post2) in
  Cases (decomp1 Post1) of
  | (Qval (exist result Post3)) =>
    let (result0, Post5) =
      let (result0, Post6) = (exist_1 [result0: Z]`result0 = 1` `2` Post3) in
      (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
      (Exn unit result0) Post6) in
    Cases (decomp1 Post5) of
    | (Qval (exist result0 Post7)) =>
      (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
      (Val Z result0) Post7)
    | (Qexn result0 Post8) =>
      (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
      (Exn unit result0) Post8)
    end
  | (Qexn result Post4) =>
    (exist_1 (qcomb [result0: Z]`result0 = 1` [result0: unit]False) (Exn unit
                                                                    result)
    Post4)
  end.

Lemma p4_po_1 : 
  (Test1: false = true)
  `2 = 1`.
Proof.
Intro H; Discriminate H.
Save.


Definition p4 := (* validation *)
  let (result, Post1) = (exist_1 [result: bool]result = true true
    (refl_equal ? true)) in
  (Cases (btest [result:bool]result = true result Post1) of
  | (left Test2) =>
      let (result0, Post7) =
        let (result0, Post8) = (exist_1 [result0: Z]`result0 = 1` `1`
          (refl_equal ? `1`)) in
        (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
        (Exn unit result0) Post8) in
      Cases (decomp1 Post7) of
      | (Qval (exist result0 Post9)) =>
        (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
        (Val Z result0) Post9)
      | (Qexn result0 Post10) =>
        (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
        (Exn unit result0) Post10)
      end
  | (right Test1) =>
      let (result0, Post3) =
        let (result0, Post4) = (exist_1 [result0: Z]`result0 = 1` `2`
          (p4_po_1 Test1)) in
        (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
        (Exn unit result0) Post4) in
      Cases (decomp1 Post3) of
      | (Qval (exist result0 Post5)) =>
        (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
        (Val Z result0) Post5)
      | (Qexn result0 Post6) =>
        (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
        (Exn unit result0) Post6)
      end end).

Lemma p5_po_1 : 
  (Test1: false = true)
  False.
Proof.
Intro H; Discriminate H.
Save.


Definition p5 := (* validation *)
  let (result, Post3) =
    let (result, Post1) = (exist_1 [result: bool]result = true true
      (refl_equal ? true)) in
    (Cases (btest [result:bool]result = true result Post1) of
    | (left Test2) =>
        let (result0, Post5) =
          let (result0, Post6) = (exist_1 [result0: Z]`result0 = 1` `1`
            (refl_equal ? `1`)) in
          (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
          (Exn unit result0) Post6) in
        Cases (decomp1 Post5) of
        | (Qval (exist result0 Post7)) =>
          (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
          (Val Z result0) Post7)
        | (Qexn result0 Post8) =>
          (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
          (Exn unit result0) Post8)
        end
    | (right Test1) =>
        let (result0, Post4) = (exist_1 [result0: unit]False tt
          (p5_po_1 Test1)) in
        (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
        (Val Z result0) Post4) end) in
  Cases (decomp1 Post3) of
  | (Qval (exist result Post9)) =>
    let (result0, Post11) =
      (exist_1 (qcomb [result0: unit]False [result0: unit]False) (Exn unit
                                                                   tt)
      Post9) in
    Cases (decomp1 Post11) of
    | (Qval (exist result0 Post12)) =>
      (exist_1 (qcomb [result1: unit]False
                (qcomb [result1: Z]`result1 = 1` [result1: unit]False)) 
      (Val unit (Val Z result0)) Post12)
    | (Qexn _ Post13) =>
      (exist_1 (qcomb [result1: unit]False
                (qcomb [result1: Z]`result1 = 1` [result1: unit]False)) 
      (Exn (EM Z unit) tt) Post13)
    end
  | (Qexn result Post10) =>
    (exist_1 (qcomb [result0: unit]False
              (qcomb [result0: Z]`result0 = 1` [result0: unit]False)) 
    (Val unit (Exn unit result)) Post10)
  end.

Lemma p6_po_1 : 
  (Test2: true = false)
  False.
Proof.
Intro H; Discriminate H.
Save.

Definition p6 := (* validation *)
  let (result, Post3) =
    let (result, Post1) = (exist_1 [result: bool]result = false false
      (refl_equal ? false)) in
    (Cases (btest [result:bool]result = false result Post1) of
    | (left Test2) =>
        let (result0, Post5) =
          let (result0, Post6) = (exist_1 [result0: Z]False `1`
            (p6_po_1 Test2)) in
          (exist_1 (qcomb [result1: Z]False [result1: unit]True) (Exn unit
                                                                   result0)
          Post6) in
        Cases (decomp1 Post5) of
        | (Qval (exist result0 Post7)) =>
          (exist_1 (qcomb [result1: Z]False [result1: unit]True) (Val Z
                                                                   result0)
          I)
        | (Qexn result0 Post8) =>
          (exist_1 (qcomb [result1: Z]False [result1: unit]True) (Exn unit
                                                                   result0)
          Post8)
        end
    | (right Test1) =>
        let (result0, Post4) = (exist_1 [result0: unit]True tt I) in
        (exist_1 (qcomb [result1: Z]False [result1: unit]True) (Val Z
                                                                 result0)
        I) end) in
  Cases (decomp1 Post3) of
  | (Qval (exist result Post9)) =>
    let (result0, Post11) =
      (exist_1 (qcomb [result0: unit]True [result0: unit]False) (Exn unit tt)
      I) in
    Cases (decomp1 Post11) of
    | (Qval (exist result0 Post12)) =>
      (exist_1 (qcomb [result1: unit]True
                (qcomb [result1: Z]False [result1: unit]False)) (Val unit
                                                                  (Val Z
                                                                    result0))
      Post12)
    | (Qexn _ Post13) =>
      (exist_1 (qcomb [result1: unit]True
                (qcomb [result1: Z]False [result1: unit]False)) (Exn
                                                                  (EM Z unit)
                                                                  tt) I)
    end
  | (Qexn result Post10) =>
    (exist_1 (qcomb [result0: unit]True
              (qcomb [result0: Z]False [result0: unit]False)) (Val unit
                                                                (Exn unit
                                                                  result))
    Post10)
  end.

Lemma p7_po_1 : 
  (x0: Z)
  (Post1: x0 = `1`)
  `x0 = 1`.
Proof.
Intuition.
Save.

Lemma p7_po_2 : 
  (x0: Z)
  (Post1: x0 = `1`)
  (Post4: ((x:Z) (x = `2` -> False)))
  (x1: Z)
  (Post2: x1 = `2`)
  False.
Proof.
Intuition.
Save.

Definition p7 := (* validation *)
  [x: Z]
    let (x0, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
        (refl_equal ? `1`)) in
      (exist_2 [x1: Z][result0: unit]x1 = `1` result tt Post1) in
    let (result0, Post3) =
      (exist_1 (qcomb [result0: unit]`x0 = 1` [result0: unit]
                ((x:Z) (x = `2` -> False))) (Exn unit tt)
      (p7_po_1 x0 Post1)) in
    Cases (decomp1 Post3) of
    | (Qval (exist result0 Post4)) =>
      let (x1, result1, Post2) =
        let (result1, Post2) = (exist_1 [result1: Z]result1 = `2` `2`
          (refl_equal ? `2`)) in
        (exist_2 [x2: Z][result2: unit]x2 = `2` result1 tt Post2) in
      (exist_2 [x2: Z](qcomb [result2: unit]`x2 = 1` [result2: unit]False) 
      x1 (Val unit result1) (p7_po_2 x0 Post1 Post4 x1 Post2))
    | (Qexn _ Post5) => (exist_2 [x1: Z]
      (qcomb [result1: unit]`x1 = 1` [result1: unit]False) x0 (Exn unit tt)
      Post5)
    end.

Lemma p8_po_1 : 
  (x0: Z)
  (Post1: x0 = `1`)
  `x0 = 1` /\ `x0 = 1`.
Proof.
Intuition.
Save.

Lemma p8_po_2 : 
  (x0: Z)
  (Post1: x0 = `1`)
  (Post5: ((x:Z) (x = `2` -> False)))
  (x1: Z)
  (Post2: x1 = `2`)
  False.
Proof.
Intuition.
Save.

Definition p8 := (* validation *)
  [x: Z]
    let (x0, result, Post1) =
      let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
        (refl_equal ? `1`)) in
      (exist_2 [x1: Z][result0: unit]x1 = `1` result tt Post1) in
    let (result0, Post3) =
      let (result0, Post4) = (exist_1 [result0: Z]`x0 = 1` /\
        `result0 = 1` x0 (p8_po_1 x0 Post1)) in
      (exist_1 (qcomb [result1: Z]`x0 = 1` /\ `result1 = 1` [result1: unit]
                ((x:Z) (x = `2` -> False))) (Exn unit result0)
      Post4) in
    Cases (decomp1 Post3) of
    | (Qval (exist result0 Post5)) =>
      let (x1, result1, Post2) =
        let (result1, Post2) = (exist_1 [result1: Z]result1 = `2` `2`
          (refl_equal ? `2`)) in
        (exist_2 [x2: Z][result2: unit]x2 = `2` result1 tt Post2) in
      (exist_2 [x2: Z]
      (qcomb [result2: Z]`x2 = 1` /\ `result2 = 1` [result2: unit]False) 
      x1 (Val Z result1) (p8_po_2 x0 Post1 Post5 x1 Post2))
    | (Qexn result0 Post6) => (exist_2 [x1: Z]
      (qcomb [result1: Z]`x1 = 1` /\ `result1 = 1` [result1: unit]False) 
      x0 (Exn unit result0) Post6)
    end.

Lemma p9_po_1 : 
  (x0: Z)
  (Post1: x0 = `1`)
  `x0 = 1` /\ `x0 = 1`.
Proof.
Intuition.
Save.

Definition p9 := (* validation *)
  [x: Z]
    let (x0, result, Post2) =
      let (x0, result, Post1) =
        let (result, Post1) = (exist_1 [result: Z]result = `1` `1`
          (refl_equal ? `1`)) in
        (exist_2 [x1: Z][result0: unit]x1 = `1` result tt Post1) in
      let (result0, Post3) = (exist_1 [result0: Z]`x0 = 1` /\
        `result0 = 1` x0 (p9_po_1 x0 Post1)) in
      (exist_2 [x1: Z][result1: Z]`x1 = 1` /\ `result1 = 1` x0 result0 Post3) in
    (exist_2 [x1: Z]
    (qcomb [result0: Z]`x1 = 1` /\ `result0 = 1` [result0: unit]False) 
    x0 (Exn unit result) Post2).

Definition p10 := (* validation *)
  let (result, Post1) =
    (exist_1 (qcomb [result: unit]`0 = 0` [result: Z]`result = 0`) (Exn Z tt)
    (refl_equal ? `0`)) in
  Cases (decomp1 Post1) of
  | (Qval (exist result Post2)) => (exist_1 [result0: Z]`result0 = 0` 
    result Post2)
  | (Qexn _ Post3) =>
    let (result0, Post4) = (exist_1 [result0: Z]`result0 = 0` `0`
      (refl_equal ? `0`)) in
    (exist_1 [result1: Z]`result1 = 0` result0 Post4)
  end.

Definition p11 := (* validation *)
  let (result, Post1) =
    let (result, Post2) = (exist_1 [result: Z]`result = 1` `1`
      (refl_equal ? `1`)) in
    (exist_1 (qcomb [result0: Z]`result0 = 1` [result0: Z]`result0 = 1`) 
    (Exn Z result) Post2) in
  Cases (decomp1 Post1) of
  | (Qval (exist result Post3)) => (exist_1 [result0: Z]`result0 = 1` 
    result Post3)
  | (Qexn result Post4) =>
    let (result0, Post5) = (exist_1 [result0: Z]`result0 = 1` result
      Post4) in
    (exist_1 [result1: Z]`result1 = 1` result0 Post5)
  end.

Definition p12 := (* validation *)
  let (result, Post1) =
    let (result, Post2) =
      (exist_1 (qcomb [result: unit]`2 = 2` [result: unit]`3 = 2`) (Exn unit
                                                                    tt)
      (refl_equal ? `2`)) in
    Cases (decomp1 Post2) of
    | (Qval (exist result Post3)) =>
      let (result0, Post5) =
        let (result0, Post6) = (exist_1 [result0: Z]`3 = 2` `1` Post3) in
        (exist_1 (qcomb [result1: Z]`3 = 2` [result1: unit]`1 = 2`) (Exn unit
                                                                    result0)
        Post6) in
      Cases (decomp1 Post5) of
      | (Qval (exist result0 Post7)) =>
        let (result1, Post9) = (exist_1 [result1: Z]`result1 = 2` `1`
          Post7) in
        (exist_1 (qcomb [result2: unit]`2 = 2`
                  (qcomb [result2: Z]`3 = 2` [result2: Z]`result2 = 2`)) 
        (Val unit (Val Z result1)) Post9)
      | (Qexn result0 Post8) =>
        (exist_1 (qcomb [result1: unit]`2 = 2`
                  (qcomb [result1: Z]`3 = 2` [result1: Z]`result1 = 2`)) 
        (Val unit (Exn Z result0)) Post8)
      end
    | (Qexn _ Post4) =>
      (exist_1 (qcomb [result0: unit]`2 = 2`
                (qcomb [result0: Z]`3 = 2` [result0: Z]`result0 = 2`)) 
      (Exn (EM Z Z) tt) (refl_equal ? `2`))
    end in
  Cases (decomp2 Post1) of
  | (Qval (Qval (exist result Post10))) => (exist_1 [result0: Z]
    `result0 = 2` result Post10)
  | (Qexn _ Post11) =>
    let (result0, Post12) = (exist_1 [result0: Z]`result0 = 2` `2`
      (refl_equal ? `2`)) in
    (exist_1 [result1: Z]`result1 = 2` result0 Post12)
  | (Qval (Qexn result Post13)) =>
    let (result0, Post14) = (exist_1 [result0: Z]`result0 = 2` `3` Post13) in
    (exist_1 [result1: Z]`result1 = 2` result0 Post14)
  end.

Lemma p13_po_1 : 
  ((x:Z) (x = `2` -> `x = 2`)).
Proof.
Intuition.
Save.

Lemma p13_po_2 : 
  (Post6: ((x:Z) (x = `3` -> `x = 2`)))
  (Post10: ((x:Z) (x = `1` -> `x = 2`)))
  (x0: Z)
  (Post1: x0 = `1`)
  `x0 = 2`.
Proof.
Intuition.
Save.

Lemma p13_po_3 : 
  (Post13: ((x:Z) (x = `2` -> `x = 2`)))
  (x1: Z)
  (Post2: x1 = `2`)
  `x1 = 2`.
Proof.
Intuition.
Save.

Lemma p13_po_4 : 
  (Post14: ((x:Z) (x = `3` -> `x = 2`)))
  (x1: Z)
  (Post3: x1 = `3`)
  `x1 = 2`.
Proof.
Intuition.
Save.

Definition p13 := (* validation *)
  [x: Z]
    let (x0, result, Post4) =
      let (result, Post5) =
        (exist_1 (qcomb [result: unit]((x:Z) (x = `2` -> `x = 2`))
                  [result: unit]((x:Z) (x = `3` -> `x = 2`))) (Exn unit tt)
        p13_po_1) in
      Cases (decomp1 Post5) of
      | (Qval (exist result Post6)) =>
        let (result0, Post8) =
          let (result0, Post9) = (exist_1 [result0: Z]
            ((x:Z) (x = `3` -> `x = 2`)) `1` Post6) in
          (exist_1 (qcomb [result1: Z]((x:Z) (x = `3` -> `x = 2`))
                    [result1: unit]((x:Z) (x = `1` -> `x = 2`))) (Exn unit
                                                                   result0)
          Post9) in
        Cases (decomp1 Post8) of
        | (Qval (exist result0 Post10)) =>
          let (x0, result1, Post1) =
            let (result1, Post1) = (exist_1 [result1: Z]result1 = `1` 
              `1` (refl_equal ? `1`)) in
            (exist_2 [x1: Z][result2: unit]x1 = `1` result1 tt Post1) in
          (exist_2 [x1: Z]
          (qcomb [result2: unit]((x:Z) (x = `2` -> `x = 2`))
           (qcomb [result2: Z]((x:Z) (x = `3` -> `x = 2`)) [result2: unit]
            `x1 = 2`)) x0
          (Val unit (Val Z result1)) (p13_po_2 Post6 Post10 x0 Post1))
        | (Qexn result0 Post11) => (exist_2 [x0: Z]
          (qcomb [result1: unit]((x:Z) (x = `2` -> `x = 2`))
           (qcomb [result1: Z]((x:Z) (x = `3` -> `x = 2`)) [result1: unit]
            `x0 = 2`)) x (Val unit (Exn unit result0)) Post11)
        end
      | (Qexn _ Post7) => (exist_2 [x0: Z]
        (qcomb [result0: unit]((x:Z) (x = `2` -> `x = 2`))
         (qcomb [result0: Z]((x:Z) (x = `3` -> `x = 2`)) [result0: unit]
          `x0 = 2`)) x (Exn (EM Z unit) tt) Post7)
      end in
    Cases (decomp2 Post4) of
    | (Qval (Qval (exist result Post12))) => (exist_2 [x1: Z][result0: unit]
      `x1 = 2` x0 result Post12)
    | (Qexn _ Post13) =>
      let (x1, result0, Post2) =
        let (result0, Post2) = (exist_1 [result0: Z]result0 = `2` `2`
          (refl_equal ? `2`)) in
        (exist_2 [x2: Z][result1: unit]x2 = `2` result0 tt Post2) in
      (exist_2 [x2: Z][result1: unit]`x2 = 2` x1 result0
      (p13_po_3 Post13 x1 Post2))
    | (Qval (Qexn result Post14)) =>
      let (x1, result0, Post3) =
        let (result0, Post3) = (exist_1 [result0: Z]result0 = `3` `3`
          (refl_equal ? `3`)) in
        (exist_2 [x2: Z][result1: unit]x2 = `3` result0 tt Post3) in
      (exist_2 [x2: Z][result1: unit]`x2 = 2` x1 result0
      (p13_po_4 Post14 x1 Post3))
    end.

Lemma p14_po_1 : 
  (x: Z)
  (Test1: `x <> 1`)
  ((`x = 2` -> `x = 2`)) /\
  ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
    ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)))).
Proof.
Intuition.
Save.

Lemma p14_po_2 : 
  (x: Z)
  (Post2: ((`x = 2` -> `x = 2`)) /\
          ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
            ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)))))
  (Test3: `x <> 2`)
  ((`x = 3` -> `x = 3`)) /\ ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)).
Proof.
Intuition.
Save.

Lemma p14_po_3 : 
  (x: Z)
  (Post2: ((`x = 2` -> `x = 2`)) /\
          ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
            ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)))))
  (Post1: ((`x = 3` -> `x = 3`)) /\
          ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)))
  (Test5: `x <> 3`)
  `x <> 1` /\ `x <> 2` /\ `x <> 3`.
Proof.
Intuition.
Save.

Definition p14 := (* validation *)
  [x: Z]
    let (result, Post4) =
      let (result, Bool1) =
        let (result1, Post5) = (Z_eq_bool x `1`) in
        (exist_1 [result2: bool]
        (if result2 then `x = 1` else `x <> 1`) result1 Post5) in
      (Cases (btest [result:bool](if result then `x = 1` else `x <> 1`)
              result Bool1) of
      | (left Test2) =>
          let (result0, Post6) =
            (exist_1 (qcomb [result0: unit]`x = 1` [result0: unit]
                      ((`x = 2` -> `x = 2`)) /\
                      ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
                        ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))))) 
            (Exn unit tt) Test2) in
          Cases (decomp1 Post6) of
          | (Qval (exist result0 Post2)) =>
            (exist_1 (qcomb [result1: unit]`x = 1` [result1: unit]
                      ((`x = 2` -> `x = 2`)) /\
                      ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
                        ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))))) 
            (Val unit result0) Post2)
          | (Qexn _ Post7) =>
            (exist_1 (qcomb [result1: unit]`x = 1` [result1: unit]
                      ((`x = 2` -> `x = 2`)) /\
                      ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
                        ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))))) 
            (Exn unit tt) Post7)
          end
      | (right Test1) =>
          let (result0, Post2) = (exist_1 [result0: unit]
            ((`x = 2` -> `x = 2`)) /\
            ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
              ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)))) tt
            (p14_po_1 x Test1)) in
          (exist_1 (qcomb [result1: unit]`x = 1` [result1: unit]
                    ((`x = 2` -> `x = 2`)) /\
                    ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
                      ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))))) 
          (Val unit result0) Post2) end) in
    Cases (decomp1 Post4) of
    | (Qval (exist result Post2)) =>
      let (result0, Post9) =
        let (result0, Bool2) =
          let (result2, Post10) = (Z_eq_bool x `2`) in
          (exist_1 [result3: bool]
          (if result3 then `x = 2` else `x <> 2`) result2 Post10) in
        (Cases (btest [result0:bool](if result0 then `x = 2` else `x <> 2`)
                result0 Bool2) of
        | (left Test4) =>
            let (result1, Post11) =
              (exist_1 (qcomb [result1: unit]`x = 2` [result1: unit]
                        ((`x = 3` -> `x = 3`)) /\
                        ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))) 
              (Exn unit tt) Test4) in
            Cases (decomp1 Post11) of
            | (Qval (exist result1 Post1)) =>
              (exist_1 (qcomb [result2: unit]`x = 2` [result2: unit]
                        ((`x = 3` -> `x = 3`)) /\
                        ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))) 
              (Val unit result1) Post1)
            | (Qexn _ Post12) =>
              (exist_1 (qcomb [result2: unit]`x = 2` [result2: unit]
                        ((`x = 3` -> `x = 3`)) /\
                        ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))) 
              (Exn unit tt) Post12)
            end
        | (right Test3) =>
            let (result1, Post1) = (exist_1 [result1: unit]
              ((`x = 3` -> `x = 3`)) /\
              ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)) tt
              (p14_po_2 x Post2 Test3)) in
            (exist_1 (qcomb [result2: unit]`x = 2` [result2: unit]
                      ((`x = 3` -> `x = 3`)) /\
                      ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))) 
            (Val unit result1) Post1) end) in
      Cases (decomp1 Post9) of
      | (Qval (exist result0 Post1)) =>
        let (result1, Post14) =
          let (result1, Bool3) =
            let (result3, Post15) = (Z_eq_bool x `3`) in
            (exist_1 [result4: bool]
            (if result4 then `x = 3` else `x <> 3`) result3 Post15) in
          (Cases (btest [result1:bool](if result1 then `x = 3` else `x <> 3`)
                  result1 Bool3) of
          | (left Test6) =>
              let (result2, Post17) =
                (exist_1 (qcomb [result2: unit]`x = 3` [result2: unit]
                          `x <> 1` /\ `x <> 2` /\ `x <> 3`) (Exn unit tt)
                Test6) in
              Cases (decomp1 Post17) of
              | (Qval (exist result2 Post18)) =>
                (exist_1 (qcomb [result3: unit]`x = 3` [result3: unit]
                          `x <> 1` /\ `x <> 2` /\ `x <> 3`) (Val unit
                                                              result2)
                Post18)
              | (Qexn _ Post19) =>
                (exist_1 (qcomb [result3: unit]`x = 3` [result3: unit]
                          `x <> 1` /\ `x <> 2` /\ `x <> 3`) (Exn unit tt)
                Post19)
              end
          | (right Test5) =>
              let (result2, Post16) = (exist_1 [result2: unit]`x <> 1` /\
                `x <> 2` /\ `x <> 3` tt (p14_po_3 x Post2 Post1 Test5)) in
              (exist_1 (qcomb [result3: unit]`x = 3` [result3: unit]
                        `x <> 1` /\ `x <> 2` /\ `x <> 3`) (Val unit result2)
              Post16) end) in
        Cases (decomp1 Post14) of
        | (Qval (exist result1 Post20)) =>
          let (result2, Post22) =
            (exist_1 (qcomb [result2: unit]`x <> 1` /\ `x <> 2` /\ `x <> 3`
                      [result2: unit]False) (Exn unit tt) Post20) in
          Cases (decomp1 Post22) of
          | (Qval (exist result2 Post23)) =>
            (exist_1 (qcomb [result3: unit]`x <> 1` /\ `x <> 2` /\ `x <> 3`
                      (qcomb [result3: unit]`x = 1`
                       (qcomb [result3: unit]`x = 2`
                        (qcomb [result3: unit]`x = 3` [result3: unit]False)))) 
            (Val unit (Val unit (Val unit (Val unit result2)))) Post23)
          | (Qexn _ Post24) =>
            (exist_1 (qcomb [result3: unit]`x <> 1` /\ `x <> 2` /\ `x <> 3`
                      (qcomb [result3: unit]`x = 1`
                       (qcomb [result3: unit]`x = 2`
                        (qcomb [result3: unit]`x = 3` [result3: unit]False)))) 
            (Exn (EM unit (EM unit (EM unit unit))) tt) Post24)
          end
        | (Qexn _ Post21) =>
          (exist_1 (qcomb [result2: unit]`x <> 1` /\ `x <> 2` /\ `x <> 3`
                    (qcomb [result2: unit]`x = 1`
                     (qcomb [result2: unit]`x = 2`
                      (qcomb [result2: unit]`x = 3` [result2: unit]False)))) 
          (Val unit (Val unit (Val unit (Exn unit tt)))) Post21)
        end
      | (Qexn _ Post13) =>
        (exist_1 (qcomb [result1: unit]`x <> 1` /\ `x <> 2` /\ `x <> 3`
                  (qcomb [result1: unit]`x = 1`
                   (qcomb [result1: unit]`x = 2`
                    (qcomb [result1: unit]`x = 3` [result1: unit]False)))) 
        (Val unit (Val unit (Exn (EM unit unit) tt))) Post13)
      end
    | (Qexn _ Post8) =>
      (exist_1 (qcomb [result0: unit]`x <> 1` /\ `x <> 2` /\ `x <> 3`
                (qcomb [result0: unit]`x = 1`
                 (qcomb [result0: unit]`x = 2`
                  (qcomb [result0: unit]`x = 3` [result0: unit]False)))) 
      (Val unit (Exn (EM unit (EM unit unit)) tt)) Post8)
    end.

