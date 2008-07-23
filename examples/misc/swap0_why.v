Require Import Why.
Require Import Omega.

(* Why obligation from file "swap0.mlw", line 12, characters 4-21: *)
(*Why goal*) Lemma swap1_po_1 : 
  forall (x0: Z),
  forall (y: Z),
  forall (x: Z),
  forall (HW_1: x = y),
  forall (y0: Z),
  forall (HW_2: y0 = x0),
  (x = y /\ y0 = x0).
Proof.
intuition.
Qed.



Definition swap1_functional (* validation *)
  : forall (_: unit), forall (x: Z), forall (y: Z),
    (sig_3 Z Z unit
     (fun (x0: Z) (y0: Z) (result: unit)  => (x0 = y /\ y0 = x)))
  := (fun (_: unit) (x: Z) (y: Z) =>
        let (x0, y0, result) :=
          let (x0, result) :=
            let (x0, result0, Post1) := (ref_set y x) in
            (exist_2 (fun (x1: Z) => (fun (result1: unit) => x1 = y)) (
            x0) (result0) (x0 = y)) in
          let (y0, result0) :=
            let (y0, result1, Post2) := (ref_set x y) in
            (exist_2 (fun (y1: Z) => (fun (result2: unit) => y1 = x)) (
            y0) (result1) (y0 = x)) in
          (Build_tuple_3 (x0) (y0) (result0)) in
        (Build_tuple_3 (x0) (y0) (result))).


(* Why obligation from file "swap0.mlw", line 24, characters 4-21: *)
(*Why goal*) Lemma swap2_po_1 : 
  forall (x0: Z),
  forall (y: Z),
  forall (x: Z),
  forall (HW_1: x = y),
  forall (y0: Z),
  forall (HW_2: y0 = x0),
  (x = y /\ y0 = x0).
Proof.
intuition.
Qed.



Definition swap2_functional (* validation *)
  : forall (_: unit), forall (x: Z), forall (y: Z),
    (sig_3 Z Z unit
     (fun (x0: Z) (y0: Z) (result: unit)  => (x0 = y /\ y0 = x)))
  := (fun (_: unit) (x: Z) (y: Z) =>
        let (x0, y0, result) :=
          let (x0, result) :=
            let (x0, result0, Post1) := (ref_set y x) in
            (exist_2 (fun (x1: Z) => (fun (result1: unit) => x1 = y)) (
            x0) (result0) (x0 = y)) in
          let (y0, result0) :=
            let (y0, result1, Post2) := (ref_set x y) in
            (exist_2 (fun (y1: Z) => (fun (result2: unit) => y1 = x)) (
            y0) (result1) (y0 = x)) in
          (Build_tuple_3 (x0) (y0) (result0)) in
        (Build_tuple_3 (x0) (y0) (result))).


(* Why obligation from file "swap0.mlw", line 32, characters 4-21: *)
(*Why goal*) Lemma swap3_po_1 : 
  forall (a0: Z),
  forall (b: Z),
  forall (a: Z),
  forall (HW_1: a = b),
  forall (b0: Z),
  forall (HW_2: b0 = a0),
  (a = b /\ b0 = a0).
Proof.
intuition.
Qed.




Definition swap3_functional (* validation *)
  : forall (b: Z), forall (a: Z),
    (sig_3 Z Z unit
     (fun (b0: Z) (a0: Z) (result: unit)  => (a0 = b /\ b0 = a)))
  := (fun (a: Z) (b: Z) =>
        let (a0, b0, result) :=
          let (a0, result) :=
            let (a0, result0, Post1) := (ref_set b a) in
            (exist_2 (fun (a1: Z) => (fun (result1: unit) => a1 = b)) (
            a0) (result0) (a0 = b)) in
          let (b0, result0) :=
            let (b0, result1, Post2) := (ref_set a b) in
            (exist_2 (fun (b1: Z) => (fun (result2: unit) => b1 = a)) (
            b0) (result1) (b0 = a)) in
          (Build_tuple_3 (a0) (b0) (result0)) in
        (Build_tuple_3 (a0) (b0) (result))).


Definition test_swap3_functional (* validation *)
  : forall (_: unit), (sig_1 unit (fun (result: unit)  => (True)))
  := (fun (_: unit) =>
        let (c1, result) :=
          let (c1, d1, result, H_1) :=
            let (c1, d1, result0, Post1) := (swap3 1 2) in
            (exist_3 (fun (c2: Z) =>
                      (fun (d2: Z) =>
                       (fun (result1: unit) => c2 = 2 /\ d2 = 1))) (c1) (
            d1) (result0) (c1 = 2 /\ d1 = 1)) in
          (Build_tuple_2 (c1) (result)) in
        result).


Definition call_swap3_x_y_functional (* validation *)
  : forall (_: unit), forall (x: Z), forall (y: Z),
    (sig_3 Z Z unit
     (fun (x0: Z) (y0: Z) (result: unit)  => (x0 = y /\ y0 = x)))
  := (fun (_: unit) (x: Z) (y: Z) =>
        let (x0, y0, result0, Post1) := (swap3 x y) in
        (exist_3 (fun (x1: Z) =>
                  (fun (y1: Z) => (fun (result1: unit) => x1 = y /\ y1 = x))) (
        x0) (y0) (result0) (x0 = y /\ y0 = x))).


(* Why obligation from file "swap0.mlw", line 42, characters 41-58: *)
(*Why goal*) Lemma call_swap3_y_x_po_1 : 
  forall (x0: Z),
  forall (y0: Z),
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: y = x0 /\ x = y0),
  (x = y0 /\ y = x0).
 (* call_swap3_y_x_po_1 *)
Proof.
intuition.
Qed.



Definition call_swap3_y_x_functional (* validation *)
  : forall (_: unit), forall (x: Z), forall (y: Z),
    (sig_3 Z Z unit
     (fun (x0: Z) (y0: Z) (result: unit)  => (x0 = y /\ y0 = x)))
  := (fun (_: unit) (x: Z) (y: Z) =>
        let (x0, y0, result0, Post1) := (swap3 x y) in
        (exist_3 (fun (x1: Z) =>
                  (fun (y1: Z) => (fun (result1: unit) => y1 = x /\ x1 = y))) (
        x0) (y0) (result0) (y0 = x /\ x0 = y))).


(* Why obligation from file "swap0.mlw", line 52, characters 4-21: *)
(*Why goal*) Lemma swap4_po_1 : 
  forall (a: Z),
  forall (b: Z),
  forall (tmp: Z),
  forall (HW_1: tmp = a),
  forall (a0: Z),
  forall (HW_2: a0 = b),
  forall (b0: Z),
  forall (HW_3: b0 = tmp),
  (a0 = b /\ b0 = a).
Proof.
intuition.
Qed.




Definition swap4_functional (* validation *)
  : forall (tmp: Z), forall (b: Z), forall (a: Z),
    (sig_4 Z Z Z unit
     (fun (tmp0: Z) (b0: Z) (a0: Z) (result: unit)  => (a0 = b /\ b0 = a)))
  := (fun (a: Z) (b: Z) (tmp: Z) =>
        let (tmp0, result) :=
          let (tmp0, result0, Post1) := (ref_set a tmp) in
          (exist_2 (fun (tmp1: Z) => (fun (result1: unit) => tmp1 = a)) (
          tmp0) (result0) (tmp0 = a)) in
        let (a0, b0, result0) :=
          let (a0, result0) :=
            let (a0, result1, Post2) := (ref_set b a) in
            (exist_2 (fun (a1: Z) => (fun (result2: unit) => a1 = b)) (
            a0) (result1) (a0 = b)) in
          let (b0, result1) :=
            let (b0, result2, Post3) := (ref_set tmp0 b) in
            (exist_2 (fun (b1: Z) => (fun (result3: unit) => b1 = tmp0)) (
            b0) (result2) (b0 = tmp0)) in
          (Build_tuple_3 (a0) (b0) (result1)) in
        (Build_tuple_4 (a0) (b0) (tmp0) (result0))).


Definition test_swap4_functional (* validation *)
  : forall (_: unit), forall (tmp: Z),
    (sig_2 Z unit (fun (tmp0: Z) (result: unit)  => (True)))
  := (fun (_: unit) (tmp: Z) =>
        let (c1, tmp0, result) :=
          let (c1, d1, tmp0, result, H_1) :=
            let (c1, d1, tmp0, result0, Post1) := (swap4 1 2 tmp) in
            (exist_4 (fun (c2: Z) =>
                      (fun (d2: Z) =>
                       (fun (tmp1: Z) =>
                        (fun (result1: unit) => c2 = 2 /\ d2 = 1)))) (
            c1) (d1) (tmp0) (result0) (c1 = 2 /\ d1 = 1)) in
          (Build_tuple_3 (c1) (tmp0) (result)) in
        (Build_tuple_2 (tmp0) (result))).


(* Why obligation from file "swap0.mlw", line 61, characters 48-53: *)
(*Why goal*) Lemma call_swap4_x_y_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x = 3),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_2: x0 = y /\ y0 = x),
  y0 = 3.
Proof.
intuition.
Qed.



Definition call_swap4_x_y_functional (* validation *)
  : forall (_: unit), forall (tmp: Z), forall (x: Z), forall (y: Z),
    forall (_: x = 3),
    (sig_4 Z Z Z unit
     (fun (tmp0: Z) (x0: Z) (y0: Z) (result: unit)  => (y0 = 3)))
  := (fun (_: unit) (tmp: Z) (x: Z) (y: Z) (H_1: x = 3) =>
        let (tmp0, x0, y0, result0, Post1) := (swap4 tmp x y) in
        (exist_4 (fun (tmp1: Z) =>
                  (fun (x1: Z) =>
                   (fun (y1: Z) => (fun (result1: unit) => x1 = y /\ y1 = x)))) (
        tmp0) (x0) (y0) (result0) (x0 = y /\ y0 = x))).


(* Why obligation from file "swap0.mlw", line 62, characters 48-53: *)
(*Why goal*) Lemma call_swap4_y_x_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x = 3),
  forall (x0: Z),
  forall (y0: Z),
  forall (HW_2: y0 = x /\ x0 = y),
  y0 = 3.
Proof.
intuition.
Qed.



Definition call_swap4_y_x_functional (* validation *)
  : forall (_: unit), forall (tmp: Z), forall (x: Z), forall (y: Z),
    forall (_: x = 3),
    (sig_4 Z Z Z unit
     (fun (tmp0: Z) (x0: Z) (y0: Z) (result: unit)  => (y0 = 3)))
  := (fun (_: unit) (tmp: Z) (x: Z) (y: Z) (H_1: x = 3) =>
        let (tmp0, x0, y0, result0, Post1) := (swap4 tmp x y) in
        (exist_4 (fun (tmp1: Z) =>
                  (fun (x1: Z) =>
                   (fun (y1: Z) => (fun (result1: unit) => y1 = x /\ x1 = y)))) (
        tmp0) (x0) (y0) (result0) (y0 = x /\ x0 = y))).


