
Require Import Why.

(*Why*) Parameter N : Z.

(* Why obligation from file "return.mlw", characters 143-149 *)
Lemma p_po_1 : 
  forall (t: (array Z)),
  forall (Pre5: (array_length t) = N),
  forall (result: Z),
  forall (Post2: result = 0),
  0 <= result /\
  (forall (i:Z),
   (0 <= i ->
    ((i < N ->
      ((((access t i) = 0 ->
         (forall (result:Z),
          (result = i ->
           (forall (result0:Z),
            (result0 = result ->
             (0 <= result0 /\ result0 < N -> (access t result0) = 0))))))) /\
      (((access t i) <> 0 ->
        (forall (result:unit),
         (result = tt ->
          (forall (result:Z),
           (result = (i + 1) -> 0 <= result /\ (Zwf 0 (N - result) (N - i))))))))) /\
      0 <= i /\ i < (array_length t))) /\
    ((i >= N ->
      (forall (result:Z),
       (result = N -> (0 <= result /\ result < N -> (access t result) = 0))))))).
Proof.
intuition.
Qed.

Proof.
intuition.
Qed.

Proof.
intuition.
Qed.

Proof.
intuition.
Qed.

Proof.
auto with *.
Qed.

