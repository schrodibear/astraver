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
  | (Qval (exist result0 Post2)) =>
    (exist_1 (qcomb [result1: unit]True
              (qcomb [result1: Z]False [result1: unit]False)) (Val unit
                                                                (Exn unit
                                                                  result0))
    (False_ind ? Post2))
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
  | (Qval (exist result0 Post3)) =>
    let (result1, Post5) =
      let (result1, Post6) = (exist_1 [result1: Z]`result1 = 1` `2` Post3) in
      (exist_1 (qcomb [result2: Z]`result2 = 1` [result2: unit]False) 
      (Exn unit result1) Post6) in
    Cases (decomp1 Post5) of
    | (Qval (exist result2 Post7)) =>
      (exist_1 (qcomb [result3: Z]`result3 = 1` [result3: unit]False) 
      (Val Z result2) (False_ind ? Post7))
    | (Qexn result2 Post8) =>
      (exist_1 (qcomb [result3: Z]`result3 = 1` [result3: unit]False) 
      (Exn unit result2) Post8)
    end
  | (Qexn result0 Post4) =>
    (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) (Exn unit
                                                                    result0)
    Post4)
  end.

(* Why obligation from file "good/exns.mlw", characters 446-447 *)
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
      | (Qval (exist result1 Post9)) =>
        (exist_1 (qcomb [result2: Z]`result2 = 1` [result2: unit]False) 
        (Val Z result1) (False_ind ? Post9))
      | (Qexn result1 Post10) =>
        (exist_1 (qcomb [result2: Z]`result2 = 1` [result2: unit]False) 
        (Exn unit result1) Post10)
      end
  | (right Test1) =>
      let (result0, Post3) =
        let (result0, Post4) = (exist_1 [result0: Z]`result0 = 1` `2`
          (p4_po_1 Test1)) in
        (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
        (Exn unit result0) Post4) in
      Cases (decomp1 Post3) of
      | (Qval (exist result1 Post5)) =>
        (exist_1 (qcomb [result2: Z]`result2 = 1` [result2: unit]False) 
        (Val Z result1) (False_ind ? Post5))
      | (Qexn result1 Post6) =>
        (exist_1 (qcomb [result2: Z]`result2 = 1` [result2: unit]False) 
        (Exn unit result1) Post6)
      end end).

(* Why obligation from file "good/exns.mlw", characters 501-525 *)
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
        | (Qval (exist result1 Post7)) =>
          (exist_1 (qcomb [result2: Z]`result2 = 1` [result2: unit]False) 
          (Val Z result1) (False_ind ? Post7))
        | (Qexn result1 Post8) =>
          (exist_1 (qcomb [result2: Z]`result2 = 1` [result2: unit]False) 
          (Exn unit result1) Post8)
        end
    | (right Test1) =>
        let (result0, Post4) = (exist_1 [result0: unit]False tt
          (p5_po_1 Test1)) in
        (exist_1 (qcomb [result1: Z]`result1 = 1` [result1: unit]False) 
        (Val Z result0) (False_ind ? Post4)) end) in
  Cases (decomp1 Post3) of
  | (Qval (exist result0 Post9)) =>
    let (result1, Post11) =
      (exist_1 (qcomb [result1: unit]False [result1: unit]False) (Exn unit
                                                                   tt)
      (False_ind ? Post9)) in
    Cases (decomp1 Post11) of
    | (Qval (exist result2 Post12)) =>
      (exist_1 (qcomb [result3: unit]False
                (qcomb [result3: Z]`result3 = 1` [result3: unit]False)) 
      (Val unit (Val Z result2)) (False_ind ? Post12))
    | (Qexn _ Post13) =>
      (exist_1 (qcomb [result2: unit]False
                (qcomb [result2: Z]`result2 = 1` [result2: unit]False)) 
      (Exn (EM Z unit) tt) (False_ind ? Post13))
    end
  | (Qexn result0 Post10) =>
    (exist_1 (qcomb [result1: unit]False
              (qcomb [result1: Z]`result1 = 1` [result1: unit]False)) 
    (Val unit (Exn unit result0)) Post10)
  end.

(* Why obligation from file "good/exns.mlw", characters 634-635 *)
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
          (False_ind ? Post6)) in
        Cases (decomp1 Post5) of
        | (Qval (exist result1 Post7)) =>
          (exist_1 (qcomb [result2: Z]False [result2: unit]True) (Val Z
                                                                   result1)
          I)
        | (Qexn result1 Post8) =>
          (exist_1 (qcomb [result2: Z]False [result2: unit]True) (Exn unit
                                                                   result1)
          (False_ind ? Post8))
        end
    | (right Test1) =>
        let (result0, Post4) = (exist_1 [result0: unit]True tt I) in
        (exist_1 (qcomb [result1: Z]False [result1: unit]True) (Val Z
                                                                 result0)
        I) end) in
  Cases (decomp1 Post3) of
  | (Qval (exist result0 Post9)) =>
    let (result1, Post11) =
      (exist_1 (qcomb [result1: unit]True [result1: unit]False) (Exn unit tt)
      I) in
    Cases (decomp1 Post11) of
    | (Qval (exist result2 Post12)) =>
      (exist_1 (qcomb [result3: unit]True
                (qcomb [result3: Z]False [result3: unit]False)) (Val unit
                                                                  (Val Z
                                                                    result2))
      (False_ind ? Post12))
    | (Qexn _ Post13) =>
      (exist_1 (qcomb [result2: unit]True
                (qcomb [result2: Z]False [result2: unit]False)) (Exn
                                                                  (EM Z unit)
                                                                  tt) I)
    end
  | (Qexn result0 Post10) =>
    (exist_1 (qcomb [result1: unit]True
              (qcomb [result1: Z]False [result1: unit]False)) (Val unit
                                                                (Exn unit
                                                                  result0))
    (False_ind ? Post10))
  end.

(* Why obligation from file "good/exns.mlw", characters 808-815 *)
Lemma p7_po_1 : 
  (x0: Z)
  (Post1: x0 = `1`)
  `x0 = 1`.
Proof.
Intuition.
Save.

(* Why obligation from file "good/exns.mlw", characters 794-850 *)
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
    | (Qval (exist result1 Post4)) =>
      let (x1, result2, Post2) =
        let (result2, Post2) = (exist_1 [result2: Z]result2 = `2` `2`
          (refl_equal ? `2`)) in
        (exist_2 [x2: Z][result3: unit]x2 = `2` result2 tt Post2) in
      (exist_2 [x2: Z](qcomb [result3: unit]`x2 = 1` [result3: unit]False) 
      x1 (Val unit result2) (p7_po_2 x0 Post1 Post4 x1 Post2))
    | (Qexn _ Post5) => (exist_2 [x1: Z]
      (qcomb [result1: unit]`x1 = 1` [result1: unit]False) x0 (Exn unit tt)
      Post5)
    end.

(* Why obligation from file "good/exns.mlw", characters 887-889 *)
Lemma p8_po_1 : 
  (x0: Z)
  (Post1: x0 = `1`)
  `x0 = 1` /\ `x0 = 1`.
Proof.
Intuition.
Save.

(* Why obligation from file "good/exns.mlw", characters 864-940 *)
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
    | (Qval (exist result1 Post5)) =>
      let (x1, result2, Post2) =
        let (result2, Post2) = (exist_1 [result2: Z]result2 = `2` `2`
          (refl_equal ? `2`)) in
        (exist_2 [x2: Z][result3: unit]x2 = `2` result2 tt Post2) in
      (exist_2 [x2: Z]
      (qcomb [result3: Z]`x2 = 1` /\ `result3 = 1` [result3: unit]False) 
      x1 (Val Z result2) (p8_po_2 x0 Post1 Post5 x1 Post2))
    | (Qexn result1 Post6) => (exist_2 [x1: Z]
      (qcomb [result2: Z]`x1 = 1` /\ `result2 = 1` [result2: unit]False) 
      x0 (Exn unit result1) Post6)
    end.

(* Why obligation from file "good/exns.mlw", characters 975-977 *)
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
  | (Qval (exist result0 Post2)) => (exist_1 [result1: Z]
    `result1 = 0` result0 Post2)
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
  | (Qval (exist result0 Post3)) => (exist_1 [result1: Z]
    `result1 = 1` result0 Post3)
  | (Qexn result0 Post4) =>
    let (result1, Post5) = (exist_1 [result1: Z]`result1 = 1` result0
      Post4) in
    (exist_1 [result2: Z]`result2 = 1` result1 Post5)
  end.

Definition p12 := (* validation *)
  let (result, Post1) =
    let (result, Post2) =
      (exist_1 (qcomb [result: unit]`2 = 2` [result: unit]`3 = 2`) (Exn unit
                                                                    tt)
      (refl_equal ? `2`)) in
    Cases (decomp1 Post2) of
    | (Qval (exist result0 Post3)) =>
      let (result1, Post5) =
        let (result1, Post6) = (exist_1 [result1: Z]`3 = 2` `1` Post3) in
        (exist_1 (qcomb [result2: Z]`3 = 2` [result2: unit]`1 = 2`) (Exn unit
                                                                    result1)
        Post6) in
      Cases (decomp1 Post5) of
      | (Qval (exist result2 Post7)) =>
        let (result3, Post9) = (exist_1 [result3: Z]`result3 = 2` `1`
          Post7) in
        (exist_1 (qcomb [result4: unit]`2 = 2`
                  (qcomb [result4: Z]`3 = 2` [result4: Z]`result4 = 2`)) 
        (Val unit (Val Z result3)) Post9)
      | (Qexn result2 Post8) =>
        (exist_1 (qcomb [result3: unit]`2 = 2`
                  (qcomb [result3: Z]`3 = 2` [result3: Z]`result3 = 2`)) 
        (Val unit (Exn Z result2)) Post8)
      end
    | (Qexn _ Post4) =>
      (exist_1 (qcomb [result0: unit]`2 = 2`
                (qcomb [result0: Z]`3 = 2` [result0: Z]`result0 = 2`)) 
      (Exn (EM Z Z) tt) (refl_equal ? `2`))
    end in
  Cases (decomp2 Post1) of
  | (Qval (Qval (exist result0 Post10))) => (exist_1 [result1: Z]
    `result1 = 2` result0 Post10)
  | (Qexn _ Post11) =>
    let (result0, Post12) = (exist_1 [result0: Z]`result0 = 2` `2`
      (refl_equal ? `2`)) in
    (exist_1 [result1: Z]`result1 = 2` result0 Post12)
  | (Qval (Qexn result0 Post13)) =>
    let (result1, Post14) = (exist_1 [result1: Z]`result1 = 2` `3` Post13) in
    (exist_1 [result2: Z]`result2 = 2` result1 Post14)
  end.

(* Why obligation from file "good/exns.mlw", characters 1309-1316 *)
Lemma p13_po_1 : 
  ((x:Z) (x = `2` -> `x = 2`)).
Proof.
Intuition.
Save.

(* Why obligation from file "good/exns.mlw", characters 1303-1341 *)
Lemma p13_po_2 : 
  (Post6: ((x:Z) (x = `3` -> `x = 2`)))
  (Post10: ((x:Z) (x = `1` -> `x = 2`)))
  (x0: Z)
  (Post1: x0 = `1`)
  `x0 = 2`.
Proof.
Intuition.
Save.

(* Why obligation from file "good/exns.mlw", characters 1294-1399 *)
Lemma p13_po_3 : 
  (Post13: ((x:Z) (x = `2` -> `x = 2`)))
  (x1: Z)
  (Post2: x1 = `2`)
  `x1 = 2`.
Proof.
Intuition.
Save.

(* Why obligation from file "good/exns.mlw", characters 1294-1399 *)
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
      | (Qval (exist result0 Post6)) =>
        let (result1, Post8) =
          let (result1, Post9) = (exist_1 [result1: Z]
            ((x:Z) (x = `3` -> `x = 2`)) `1` Post6) in
          (exist_1 (qcomb [result2: Z]((x:Z) (x = `3` -> `x = 2`))
                    [result2: unit]((x:Z) (x = `1` -> `x = 2`))) (Exn unit
                                                                   result1)
          Post9) in
        Cases (decomp1 Post8) of
        | (Qval (exist result2 Post10)) =>
          let (x0, result3, Post1) =
            let (result3, Post1) = (exist_1 [result3: Z]result3 = `1` 
              `1` (refl_equal ? `1`)) in
            (exist_2 [x1: Z][result4: unit]x1 = `1` result3 tt Post1) in
          (exist_2 [x1: Z]
          (qcomb [result4: unit]((x:Z) (x = `2` -> `x = 2`))
           (qcomb [result4: Z]((x:Z) (x = `3` -> `x = 2`)) [result4: unit]
            `x1 = 2`)) x0
          (Val unit (Val Z result3)) (p13_po_2 Post6 Post10 x0 Post1))
        | (Qexn result2 Post11) => (exist_2 [x0: Z]
          (qcomb [result3: unit]((x:Z) (x = `2` -> `x = 2`))
           (qcomb [result3: Z]((x:Z) (x = `3` -> `x = 2`)) [result3: unit]
            `x0 = 2`)) x (Val unit (Exn unit result2)) Post11)
        end
      | (Qexn _ Post7) => (exist_2 [x0: Z]
        (qcomb [result0: unit]((x:Z) (x = `2` -> `x = 2`))
         (qcomb [result0: Z]((x:Z) (x = `3` -> `x = 2`)) [result0: unit]
          `x0 = 2`)) x (Exn (EM Z unit) tt) Post7)
      end in
    Cases (decomp2 Post4) of
    | (Qval (Qval (exist result0 Post12))) => (exist_2 [x1: Z][result1: unit]
      `x1 = 2` x0 result0 Post12)
    | (Qexn _ Post13) =>
      let (x1, result0, Post2) =
        let (result0, Post2) = (exist_1 [result0: Z]result0 = `2` `2`
          (refl_equal ? `2`)) in
        (exist_2 [x2: Z][result1: unit]x2 = `2` result0 tt Post2) in
      (exist_2 [x2: Z][result1: unit]`x2 = 2` x1 result0
      (p13_po_3 Post13 x1 Post2))
    | (Qval (Qexn result0 Post14)) =>
      let (x1, result1, Post3) =
        let (result1, Post3) = (exist_1 [result1: Z]result1 = `3` `3`
          (refl_equal ? `3`)) in
        (exist_2 [x2: Z][result2: unit]x2 = `3` result1 tt Post3) in
      (exist_2 [x2: Z][result2: unit]`x2 = 2` x1 result1
      (p13_po_4 Post14 x1 Post3))
    end.

(* Why obligation from file "good/exns.mlw", characters 1465-1488 *)
Lemma p14_po_1 : 
  (x: Z)
  (Test1: `x <> 1`)
  ((`x = 2` -> `x = 2`)) /\
  ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
    ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)))).
Proof.
Intuition.
Save.

(* Why obligation from file "good/exns.mlw", characters 1494-1517 *)
Lemma p14_po_2 : 
  (x: Z)
  (Post10: ((`x = 2` -> `x = 2`)) /\
           ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
             ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)))))
  (Test3: `x <> 2`)
  ((`x = 3` -> `x = 3`)) /\ ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)).
Proof.
Intuition.
Save.

(* Why obligation from file "good/exns.mlw", characters 1523-1546 *)
Lemma p14_po_3 : 
  (x: Z)
  (Post10: ((`x = 2` -> `x = 2`)) /\
           ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
             ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)))))
  (Post18: ((`x = 3` -> `x = 3`)) /\
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
          let (result0, Post7) =
            (exist_1 (qcomb [result0: unit]`x = 1` [result0: unit]
                      ((`x = 2` -> `x = 2`)) /\
                      ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
                        ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))))) 
            (Exn unit tt) Test2) in
          Cases (decomp1 Post7) of
          | (Qval (exist result1 Post8)) =>
            (exist_1 (qcomb [result2: unit]`x = 1` [result2: unit]
                      ((`x = 2` -> `x = 2`)) /\
                      ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
                        ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))))) 
            (Val unit result1) Post8)
          | (Qexn _ Post9) =>
            (exist_1 (qcomb [result1: unit]`x = 1` [result1: unit]
                      ((`x = 2` -> `x = 2`)) /\
                      ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
                        ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))))) 
            (Exn unit tt) Post9)
          end
      | (right Test1) =>
          let (result0, Post6) = (exist_1 [result0: unit]
            ((`x = 2` -> `x = 2`)) /\
            ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
              ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)))) tt
            (p14_po_1 x Test1)) in
          (exist_1 (qcomb [result1: unit]`x = 1` [result1: unit]
                    ((`x = 2` -> `x = 2`)) /\
                    ((`x <> 2` -> ((`x = 3` -> `x = 3`)) /\
                      ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))))) 
          (Val unit result0) Post6) end) in
    Cases (decomp1 Post4) of
    | (Qval (exist result0 Post10)) =>
      let (result1, Post12) =
        let (result1, Bool2) =
          let (result3, Post13) = (Z_eq_bool x `2`) in
          (exist_1 [result4: bool]
          (if result4 then `x = 2` else `x <> 2`) result3 Post13) in
        (Cases (btest [result1:bool](if result1 then `x = 2` else `x <> 2`)
                result1 Bool2) of
        | (left Test4) =>
            let (result2, Post15) =
              (exist_1 (qcomb [result2: unit]`x = 2` [result2: unit]
                        ((`x = 3` -> `x = 3`)) /\
                        ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))) 
              (Exn unit tt) Test4) in
            Cases (decomp1 Post15) of
            | (Qval (exist result3 Post16)) =>
              (exist_1 (qcomb [result4: unit]`x = 2` [result4: unit]
                        ((`x = 3` -> `x = 3`)) /\
                        ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))) 
              (Val unit result3) Post16)
            | (Qexn _ Post17) =>
              (exist_1 (qcomb [result3: unit]`x = 2` [result3: unit]
                        ((`x = 3` -> `x = 3`)) /\
                        ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))) 
              (Exn unit tt) Post17)
            end
        | (right Test3) =>
            let (result2, Post14) = (exist_1 [result2: unit]
              ((`x = 3` -> `x = 3`)) /\
              ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`)) tt
              (p14_po_2 x Post10 Test3)) in
            (exist_1 (qcomb [result3: unit]`x = 2` [result3: unit]
                      ((`x = 3` -> `x = 3`)) /\
                      ((`x <> 3` -> `x <> 1` /\ `x <> 2` /\ `x <> 3`))) 
            (Val unit result2) Post14) end) in
      Cases (decomp1 Post12) of
      | (Qval (exist result2 Post18)) =>
        let (result3, Post20) =
          let (result3, Bool3) =
            let (result5, Post21) = (Z_eq_bool x `3`) in
            (exist_1 [result6: bool]
            (if result6 then `x = 3` else `x <> 3`) result5 Post21) in
          (Cases (btest [result3:bool](if result3 then `x = 3` else `x <> 3`)
                  result3 Bool3) of
          | (left Test6) =>
              let (result4, Post23) =
                (exist_1 (qcomb [result4: unit]`x = 3` [result4: unit]
                          `x <> 1` /\ `x <> 2` /\ `x <> 3`) (Exn unit tt)
                Test6) in
              Cases (decomp1 Post23) of
              | (Qval (exist result5 Post24)) =>
                (exist_1 (qcomb [result6: unit]`x = 3` [result6: unit]
                          `x <> 1` /\ `x <> 2` /\ `x <> 3`) (Val unit
                                                              result5)
                Post24)
              | (Qexn _ Post25) =>
                (exist_1 (qcomb [result5: unit]`x = 3` [result5: unit]
                          `x <> 1` /\ `x <> 2` /\ `x <> 3`) (Exn unit tt)
                Post25)
              end
          | (right Test5) =>
              let (result4, Post22) = (exist_1 [result4: unit]`x <> 1` /\
                `x <> 2` /\ `x <> 3` tt (p14_po_3 x Post10 Post18 Test5)) in
              (exist_1 (qcomb [result5: unit]`x = 3` [result5: unit]
                        `x <> 1` /\ `x <> 2` /\ `x <> 3`) (Val unit result4)
              Post22) end) in
        Cases (decomp1 Post20) of
        | (Qval (exist result4 Post26)) =>
          let (result5, Post28) =
            (exist_1 (qcomb [result5: unit]`x <> 1` /\ `x <> 2` /\ `x <> 3`
                      [result5: unit]False) (Exn unit tt) Post26) in
          Cases (decomp1 Post28) of
          | (Qval (exist result6 Post29)) =>
            (exist_1 (qcomb [result7: unit]`x <> 1` /\ `x <> 2` /\ `x <> 3`
                      (qcomb [result7: unit]`x = 1`
                       (qcomb [result7: unit]`x = 2`
                        (qcomb [result7: unit]`x = 3` [result7: unit]False)))) 
            (Val unit (Val unit (Val unit (Val unit result6))))
            (False_ind ? Post29))
          | (Qexn _ Post30) =>
            (exist_1 (qcomb [result6: unit]`x <> 1` /\ `x <> 2` /\ `x <> 3`
                      (qcomb [result6: unit]`x = 1`
                       (qcomb [result6: unit]`x = 2`
                        (qcomb [result6: unit]`x = 3` [result6: unit]False)))) 
            (Exn (EM unit (EM unit (EM unit unit))) tt) Post30)
          end
        | (Qexn _ Post27) =>
          (exist_1 (qcomb [result4: unit]`x <> 1` /\ `x <> 2` /\ `x <> 3`
                    (qcomb [result4: unit]`x = 1`
                     (qcomb [result4: unit]`x = 2`
                      (qcomb [result4: unit]`x = 3` [result4: unit]False)))) 
          (Val unit (Val unit (Val unit (Exn unit tt)))) Post27)
        end
      | (Qexn _ Post19) =>
        (exist_1 (qcomb [result2: unit]`x <> 1` /\ `x <> 2` /\ `x <> 3`
                  (qcomb [result2: unit]`x = 1`
                   (qcomb [result2: unit]`x = 2`
                    (qcomb [result2: unit]`x = 3` [result2: unit]False)))) 
        (Val unit (Val unit (Exn (EM unit unit) tt))) Post19)
      end
    | (Qexn _ Post11) =>
      (exist_1 (qcomb [result0: unit]`x <> 1` /\ `x <> 2` /\ `x <> 3`
                (qcomb [result0: unit]`x = 1`
                 (qcomb [result0: unit]`x = 2`
                  (qcomb [result0: unit]`x = 3` [result0: unit]False)))) 
      (Val unit (Exn (EM unit (EM unit unit)) tt)) Post11)
    end.

