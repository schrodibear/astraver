(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.

(* Why obligation from file "good-c/see.c", characters 122-123 *)
Lemma f_po_1 : 
  (b: Z)
  (b0: Z)
  (Post1: b0 = `1 - b`)
  `b0 = b0` /\ `b0 = 1 - b`.
Proof.
Intuition.
Save.


(* Why obligation from file "good-c/see.c", characters 196-203 *)
Lemma k_po_1 : 
  (b0: Z)
  (Post1: b0 = `1`)
  (b3: Z)
  (c_aux_1: Z)
  (Post4: `c_aux_1 = b3` /\ `b3 = 1 - b0`)
  (b4: Z)
  (c_aux_2: Z)
  (Post8: `c_aux_2 = b4` /\ `b4 = 1 - b3`)
  ((result:Z)
   ((b:Z)
    (`result = b` /\ `b = 1 - b4` ->
     ((result0:Z)
      ((b0:Z)
       (`result0 = b0` /\ `b0 = 1 - b` -> `c_aux_1 + (1 - c_aux_2) = 0` /\
        `(1 - result) * result0 = 1`)))))).
Proof.
Intuition.
Subst result0 result b b0 b1 b3 b4; Ring.
Save.

(* Why obligation from file "good-c/see.c", characters 214-221 *)
Lemma k_po_2 : 
  (b0: Z)
  (Post1: b0 = `1`)
  (b4: Z)
  (b3: Z)
  (Post2: ((result:Z)
           ((b:Z)
            (`result = b` /\ `b = 1 - b4` ->
             ((result0:Z)
              ((b0:Z)
               (`result0 = b0` /\ `b0 = 1 - b` -> `b3 = 0` /\
                `(1 - result) * result0 = 1`)))))))
  (b5: Z)
  (c_aux_4: Z)
  (Post15: `c_aux_4 = b5` /\ `b5 = 1 - b4`)
  ((result:Z)
   ((b:Z)
    (`result = b` /\ `b = 1 - b5` -> `b3 = 0` /\ `(1 - c_aux_4) * result = 1`))).
Proof.
LinearIntuition.
Save.

(* Why obligation from file "good-c/see.c", characters 213-228 *)
Lemma k_po_3 : 
  (b0: Z)
  (Post1: b0 = `1`)
  (b4: Z)
  (b3: Z)
  (Post2: ((result:Z)
           ((b:Z)
            (`result = b` /\ `b = 1 - b4` ->
             ((result0:Z)
              ((b0:Z)
               (`result0 = b0` /\ `b0 = 1 - b` -> `b3 = 0` /\
                `(1 - result) * result0 = 1`)))))))
  (b5: Z)
  (c_aux_5: Z)
  (Post14: ((result:Z)
            ((b:Z)
             (`result = b` /\ `b = 1 - b5` -> `b3 = 0` /\
              `c_aux_5 * result = 1`))))
  (b6: Z)
  (c_aux_6: Z)
  (Post19: `c_aux_6 = b6` /\ `b6 = 1 - b5`)
  `b3 = 0` /\ `c_aux_5 * c_aux_6 = 1`.
Proof.
LinearIntuition.
Save.


