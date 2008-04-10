(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)
Require Export Why.

(*Why type*) Definition set: Set ->Set.
Admitted.

(*Why logic*) Definition set_empty : forall (A1:Set), (set A1).
Admitted.
Set Contextual Implicit.
Implicit Arguments set_empty.
Unset Contextual Implicit.

(*Why logic*) Definition set_add :
  forall (A1:Set), A1 -> (set A1) -> (set A1).
Admitted.
Implicit Arguments set_add.

(*Why logic*) Definition set_rmv :
  forall (A1:Set), A1 -> (set A1) -> (set A1).
Admitted.
Implicit Arguments set_rmv.

(*Why logic*) Definition In : forall (A1:Set), A1 -> (set A1) -> Prop.
Admitted.
Implicit Arguments In.

(*Why predicate*) Definition Is_empty (A113:Set) (s:(set A113))
  := (forall (x:A113), ~(In x s)).
Implicit Arguments Is_empty.

(*Why axiom*) Lemma set_empty_def :
  forall (A1:Set), (Is_empty (@set_empty A1)).
Admitted.

(*Why axiom*) Lemma set_add_def :
  forall (A1:Set),
  (forall (x:A1),
   (forall (y:A1),
    (forall (s:(set A1)), ((In x (set_add y s)) <-> x = y \/ (In x s))))).
Admitted.

(*Why axiom*) Lemma set_rmv_def :
  forall (A1:Set),
  (forall (x:A1),
   (forall (y:A1),
    (forall (s:(set A1)), ((In x (set_rmv y s)) <-> ~(x = y) /\ (In x s))))).
Admitted.

(*Why logic*) Definition set_card : forall (A1:Set), (set A1) -> Z.
Admitted.
Implicit Arguments set_card.

(*Why axiom*) Lemma card_set_add :
  forall (A1:Set),
  (forall (x:A1),
   (forall (s:(set A1)),
    (~(In x s) -> (set_card (set_add x s)) = (1 + (set_card s))))).
Admitted.

(*Why axiom*) Lemma card_set_rmv :
  forall (A1:Set),
  (forall (x:A1),
   (forall (s:(set A1)),
    ((In x s) -> (set_card s) = (1 + (set_card (set_rmv x s)))))).
Admitted.

(*Why type*) Definition int_int: Set.
exact (Z * Z)%type.
Defined.

(*Why logic*) Definition pair : Z -> Z -> int_int.
exact (@pair Z Z).
Defined.

(*Why logic*) Definition fst : int_int -> Z.
exact (@fst Z Z).
Defined.

(*Why logic*) Definition snd : int_int -> Z.
exact (@snd Z Z).
Defined.

(*Why axiom*) Lemma pair_1 :
  (forall (x:Z), (forall (y:Z), (fst (pair x y)) = x)).
auto.
Qed.

(*Why axiom*) Lemma pair_2 :
  (forall (x:Z), (forall (y:Z), (snd (pair x y)) = y)).
auto.
Qed.

(*Why axiom*) Lemma pair_e :
  (forall (x:int_int), x = (pair (fst x) (snd x))).
destruct x; auto.
Qed.

(*Why predicate*) Definition Min  (e:int_int) (pq:(set int_int))
  := (In e pq) /\ (forall (x:int_int), ((In x pq) -> (snd e) <= (snd x))).

(*Why logic*) Definition N : Z.
Admitted.

(*Why logic*) Definition g : Z -> Z -> bool.
Admitted.

(*Why axiom*) Lemma g_finite :
  (forall (x:Z),
   (forall (y:Z), ((g x y) = true -> (0 <= x /\ x < N) /\ 0 <= y /\ y < N))).
Admitted.

(*Why logic*) Definition weight : Z -> Z -> Z.
Admitted.

(*Why axiom*) Lemma weight_nonneg :
  (forall (x:Z), (forall (y:Z), (weight x y) >= 0)).
Admitted.

(*Why logic*) Definition path : Z -> Z -> Z -> Prop.
Admitted.

(*Why axiom*) Lemma path_nil : (forall (x:Z), (path x x 0)).
Admitted.

(*Why axiom*) Lemma path_cons :
  (forall (x:Z),
   (forall (y:Z),
    (forall (z:Z),
     (forall (d:Z),
      ((path x y d) -> ((g y z) = true -> (path x z (d + (weight y z))))))))).
Admitted.

(*Why axiom*) Lemma length_nonneg :
  (forall (x:Z), (forall (y:Z), (forall (d:Z), ((path x y d) -> d >= 0)))).
Admitted.

(*Why predicate*) Definition shortest_path  (x:Z) (y:Z) (d:Z)
  := (path x y d) /\ (forall (d':Z), ((path x y d') -> d <= d')).

(*Why axiom*) Lemma path_inversion :
  (forall (src:Z),
   (forall (v:Z),
    (forall (d:Z),
     ((path src v d) -> v = src /\ d = 0 \/
      (exists v':Z, (path src v' (d - (weight v' v))) /\ (g v' v) = true))))).
Admitted.

(*Why axiom*) Lemma path_shortest_path :
  (forall (src:Z),
   (forall (v:Z),
    (forall (d:Z),
     ((path src v d) -> (exists d':Z, (shortest_path src v d') /\ d' <= d))))).
Admitted.

(*Why axiom*) Lemma main_lemma :
  (forall (src:Z),
   (forall (v:Z),
    (forall (d:Z),
     ((path src v d) ->
      (~(shortest_path src v d) ->
       (exists v':Z,
        (exists d':Z, (shortest_path src v' d') /\ (g v' v) = true /\
         (d' + (weight v' v)) < d))))))).
Admitted.

(*Why predicate*) Definition lex2  (x:int_int) (y:int_int)
  := (fst x) < (fst y) \/ (fst x) = (fst y) /\ (snd x) < (snd y).

(*Why predicate*) Definition Inv  (src:Z) (visited:(set Z)) (pq:(set int_int))
  := (forall (d:Z), ((In (pair src d) pq) -> (In src visited) \/ d = 0)) /\
     (forall (e:int_int), ((In e pq) -> (path src (fst e) (snd e)))) /\
     (forall (m:int_int),
      ((Min m pq) ->
       (forall (x:Z),
        (forall (d:Z),
         ((shortest_path src x d) -> (d < (snd m) -> (In x visited))))))) /\
     (forall (x:Z),
      (forall (y:Z),
       ((In x visited) ->
        ((g x y) = true -> (In y visited) \/
         (forall (d:Z),
          ((shortest_path src x d) -> (In (pair y (d + (weight x y))) pq))))))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma shortest_path_po_1 : 
  forall (src: Z),
  forall (dst: Z),
  forall (pq: (set int_int)),
  forall (visited: (set Z)),
  forall (HW_1: (0 <= src /\ src < N) /\ (0 <= dst /\ dst < N) /\
                (Is_empty visited) /\ (Is_empty pq)),
  forall (pq0: (set int_int)),
  forall (HW_2: pq0 = (set_add (pair src 0) pq)),
  (well_founded lex2).
Proof.
(* FILL PROOF HERE *)
Admitted.

(* Why obligation from file "dijkstra.why", line 148, characters 16-61: *)
(*Why goal*) Lemma shortest_path_po_2 : 
  forall (src: Z),
  forall (dst: Z),
  forall (pq: (set int_int)),
  forall (visited: (set Z)),
  forall (HW_1: (0 <= src /\ src < N) /\ (0 <= dst /\ dst < N) /\
                (Is_empty visited) /\ (Is_empty pq)),
  forall (pq0: (set int_int)),
  forall (HW_2: pq0 = (set_add (pair src 0) pq)),
  ((Inv src visited pq0) /\ ~(In dst visited)).
Proof.
(* FILL PROOF HERE *)
Admitted.

(* Why obligation from file "dijkstra.why", line 148, characters 16-61: *)
(*Why goal*) Lemma shortest_path_po_3 : 
  forall (src: Z),
  forall (dst: Z),
  forall (pq: (set int_int)),
  forall (visited: (set Z)),
  forall (HW_1: (0 <= src /\ src < N) /\ (0 <= dst /\ dst < N) /\
                (Is_empty visited) /\ (Is_empty pq)),
  forall (pq0: (set int_int)),
  forall (HW_2: pq0 = (set_add (pair src 0) pq)),
  forall (pq1: (set int_int)),
  forall (visited0: (set Z)),
  forall (HW_3: (Inv src visited0 pq1) /\ ~(In dst visited0)),
  forall (HW_6: ~(Is_empty pq1)),
  forall (result: int_int),
  forall (pq2: (set int_int)),
  forall (HW_7: (Min result pq1) /\ pq2 = (set_rmv result pq1)),
  forall (HW_8: (In (fst result) visited0)),
  ((Inv src visited0 pq2) /\ ~(In dst visited0)).
Proof.
(* FILL PROOF HERE *)
Admitted.

(* Why obligation from file "dijkstra.why", line 149, characters 14-55: *)
(*Why goal*) Lemma shortest_path_po_4 : 
  forall (src: Z),
  forall (dst: Z),
  forall (pq: (set int_int)),
  forall (visited: (set Z)),
  forall (HW_1: (0 <= src /\ src < N) /\ (0 <= dst /\ dst < N) /\
                (Is_empty visited) /\ (Is_empty pq)),
  forall (pq0: (set int_int)),
  forall (HW_2: pq0 = (set_add (pair src 0) pq)),
  forall (pq1: (set int_int)),
  forall (visited0: (set Z)),
  forall (HW_3: (Inv src visited0 pq1) /\ ~(In dst visited0)),
  forall (HW_6: ~(Is_empty pq1)),
  forall (result: int_int),
  forall (pq2: (set int_int)),
  forall (HW_7: (Min result pq1) /\ pq2 = (set_rmv result pq1)),
  forall (HW_8: (In (fst result) visited0)),
  (lex2
   (pair (N - (set_card visited0)) (set_card pq2)) (pair
                                                    (N - (set_card visited0)) (
                                                    set_card pq1))).
Proof.
(* FILL PROOF HERE *)
Admitted.

(* Why obligation from file "dijkstra.why", line 154, characters 15-39: *)
(*Why goal*) Lemma shortest_path_po_5 : 
  forall (src: Z),
  forall (dst: Z),
  forall (pq: (set int_int)),
  forall (visited: (set Z)),
  forall (HW_1: (0 <= src /\ src < N) /\ (0 <= dst /\ dst < N) /\
                (Is_empty visited) /\ (Is_empty pq)),
  forall (pq0: (set int_int)),
  forall (HW_2: pq0 = (set_add (pair src 0) pq)),
  forall (pq1: (set int_int)),
  forall (visited0: (set Z)),
  forall (HW_3: (Inv src visited0 pq1) /\ ~(In dst visited0)),
  forall (HW_6: ~(Is_empty pq1)),
  forall (result: int_int),
  forall (pq2: (set int_int)),
  forall (HW_7: (Min result pq1) /\ pq2 = (set_rmv result pq1)),
  forall (HW_9: ~(In (fst result) visited0)),
  (shortest_path src (fst result) (snd result)).
Proof.
  unfold Inv; intuition.
  generalize (H8 result H9); clear H8.
  unfold Min in H9; red; intuition.
  assert (case : fst result = src \/ fst result <> src). omega.  destruct case.
  destruct result as (v,d).
  subst src.
  generalize (H7 d H12); clear H7; destruct 1.
  elim (HW_9 H7).
  simpl; subst d.
  apply Zge_le. apply length_nonneg with v v; assumption.
 (* v <> src *)
 destruct result as (v,d); simpl in *|-*.
  destruct (path_inversion _ _ _ H9); intuition.
  destruct H15 as (v',(hv'1,hv'2)).
  assert (case : d' < d \/ d <= d'). omega. intuition.
  generalize (path_shortest_path _ _ _ hv'1); intros (d'',(h''1,h''2)).
  assert (In v' visited0).
  apply H8 with d''; auto.
  assert (weight v' v >= 0).
  apply weight_nonneg.
 omega.
  generalize (H10 v' v H16 hv'2); intuition.
  assert (h := H18 d'' h''1).
  pose (H13 _ h).
  simpl in z. omega.
Save.

(* Why obligation from file "dijkstra.why", line 167, characters 20-49: *)
(*Why goal*) Lemma shortest_path_po_6 : 
  forall (src: Z),
  forall (dst: Z),
  forall (pq: (set int_int)),
  forall (visited: (set Z)),
  forall (HW_1: (0 <= src /\ src < N) /\ (0 <= dst /\ dst < N) /\
                (Is_empty visited) /\ (Is_empty pq)),
  forall (pq0: (set int_int)),
  forall (HW_2: pq0 = (set_add (pair src 0) pq)),
  forall (pq1: (set int_int)),
  forall (visited0: (set Z)),
  forall (HW_3: (Inv src visited0 pq1) /\ ~(In dst visited0)),
  forall (HW_6: ~(Is_empty pq1)),
  forall (result: int_int),
  forall (pq2: (set int_int)),
  forall (HW_7: (Min result pq1) /\ pq2 = (set_rmv result pq1)),
  forall (HW_9: ~(In (fst result) visited0)),
  forall (HW_10: (shortest_path src (fst result) (snd result))),
  forall (visited1: (set Z)),
  forall (HW_11: visited1 = (set_add (fst result) visited0)),
  forall (HW_12: (fst result) = dst),
  (shortest_path src dst (snd result)).
Proof.
  unfold Inv; intuition; subst dst.
  assumption.
Save.

(* Why obligation from file "dijkstra.why", line 159, characters 20-41: *)
(*Why goal*) Lemma shortest_path_po_7 : 
  forall (src: Z),
  forall (dst: Z),
  forall (pq: (set int_int)),
  forall (visited: (set Z)),
  forall (HW_1: (0 <= src /\ src < N) /\ (0 <= dst /\ dst < N) /\
                (Is_empty visited) /\ (Is_empty pq)),
  forall (pq0: (set int_int)),
  forall (HW_2: pq0 = (set_add (pair src 0) pq)),
  forall (pq1: (set int_int)),
  forall (visited0: (set Z)),
  forall (HW_3: (Inv src visited0 pq1) /\ ~(In dst visited0)),
  forall (HW_6: ~(Is_empty pq1)),
  forall (result: int_int),
  forall (pq2: (set int_int)),
  forall (HW_7: (Min result pq1) /\ pq2 = (set_rmv result pq1)),
  forall (HW_9: ~(In (fst result) visited0)),
  forall (HW_10: (shortest_path src (fst result) (snd result))),
  forall (visited1: (set Z)),
  forall (HW_11: visited1 = (set_add (fst result) visited0)),
  forall (HW_13: (fst result) <> dst),
  (Inv src visited1 pq2).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "dijkstra.why", line 154, characters 15-39: *)
(*Why goal*) Lemma shortest_path_po_8 : 
  forall (src: Z),
  forall (dst: Z),
  forall (pq: (set int_int)),
  forall (visited: (set Z)),
  forall (HW_1: (0 <= src /\ src < N) /\ (0 <= dst /\ dst < N) /\
                (Is_empty visited) /\ (Is_empty pq)),
  forall (pq0: (set int_int)),
  forall (HW_2: pq0 = (set_add (pair src 0) pq)),
  forall (pq1: (set int_int)),
  forall (visited0: (set Z)),
  forall (HW_3: (Inv src visited0 pq1) /\ ~(In dst visited0)),
  forall (HW_6: ~(Is_empty pq1)),
  forall (result: int_int),
  forall (pq2: (set int_int)),
  forall (HW_7: (Min result pq1) /\ pq2 = (set_rmv result pq1)),
  forall (HW_9: ~(In (fst result) visited0)),
  forall (HW_10: (shortest_path src (fst result) (snd result))),
  forall (visited1: (set Z)),
  forall (HW_11: visited1 = (set_add (fst result) visited0)),
  forall (HW_13: (fst result) <> dst),
  forall (pq3: (set int_int)),
  forall (w: Z),
  forall (HW_14: (Inv src visited1 pq3)),
  forall (HW_15: w < N),
  ((if (g (fst result) w)
    then (((In w visited1) ->
           (forall (w0:Z),
            (w0 = (w + 1) -> (Inv src visited1 pq3) /\
             (Zwf 0 (N - w0) (N - w)))))) /\
    ((~(In w visited1) ->
      (forall (pq:(set int_int)),
       (pq = (set_add (pair w ((snd result) + (weight (fst result) w))) pq3) ->
        (forall (w0:Z),
         (w0 = (w + 1) -> (Inv src visited1 pq) /\ (Zwf 0 (N - w0) (N - w))))))))
    else (forall (w0:Z),
          (w0 = (w + 1) -> (Inv src visited1 pq3) /\ (Zwf 0 (N - w0) (N - w)))))).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "dijkstra.why", line 148, characters 16-61: *)
(*Why goal*) Lemma shortest_path_po_9 : 
  forall (src: Z),
  forall (dst: Z),
  forall (pq: (set int_int)),
  forall (visited: (set Z)),
  forall (HW_1: (0 <= src /\ src < N) /\ (0 <= dst /\ dst < N) /\
                (Is_empty visited) /\ (Is_empty pq)),
  forall (pq0: (set int_int)),
  forall (HW_2: pq0 = (set_add (pair src 0) pq)),
  forall (pq1: (set int_int)),
  forall (visited0: (set Z)),
  forall (HW_3: (Inv src visited0 pq1) /\ ~(In dst visited0)),
  forall (HW_6: ~(Is_empty pq1)),
  forall (result: int_int),
  forall (pq2: (set int_int)),
  forall (HW_7: (Min result pq1) /\ pq2 = (set_rmv result pq1)),
  forall (HW_9: ~(In (fst result) visited0)),
  forall (HW_10: (shortest_path src (fst result) (snd result))),
  forall (visited1: (set Z)),
  forall (HW_11: visited1 = (set_add (fst result) visited0)),
  forall (HW_13: (fst result) <> dst),
  forall (pq3: (set int_int)),
  forall (w: Z),
  forall (HW_14: (Inv src visited1 pq3)),
  forall (HW_16: w >= N),
  ((Inv src visited1 pq3) /\ ~(In dst visited1)).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "dijkstra.why", line 149, characters 14-55: *)
(*Why goal*) Lemma shortest_path_po_10 : 
  forall (src: Z),
  forall (dst: Z),
  forall (pq: (set int_int)),
  forall (visited: (set Z)),
  forall (HW_1: (0 <= src /\ src < N) /\ (0 <= dst /\ dst < N) /\
                (Is_empty visited) /\ (Is_empty pq)),
  forall (pq0: (set int_int)),
  forall (HW_2: pq0 = (set_add (pair src 0) pq)),
  forall (pq1: (set int_int)),
  forall (visited0: (set Z)),
  forall (HW_3: (Inv src visited0 pq1) /\ ~(In dst visited0)),
  forall (HW_6: ~(Is_empty pq1)),
  forall (result: int_int),
  forall (pq2: (set int_int)),
  forall (HW_7: (Min result pq1) /\ pq2 = (set_rmv result pq1)),
  forall (HW_9: ~(In (fst result) visited0)),
  forall (HW_10: (shortest_path src (fst result) (snd result))),
  forall (visited1: (set Z)),
  forall (HW_11: visited1 = (set_add (fst result) visited0)),
  forall (HW_13: (fst result) <> dst),
  forall (pq3: (set int_int)),
  forall (w: Z),
  forall (HW_14: (Inv src visited1 pq3)),
  forall (HW_16: w >= N),
  (lex2
   (pair (N - (set_card visited1)) (set_card pq3)) (pair
                                                    (N - (set_card visited0)) (
                                                    set_card pq1))).
Proof.
(* FILL PROOF HERE *)
Save.

