(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Why

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 240-255 *)
Lemma sort4bis_po_1 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  ~(a = null) /\ 0 <= (offset a) /\ (offset a) < (length a).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 287-302 *)
Lemma sort4bis_po_2 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (intP: ((memory) Z)),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (Pre7: ~(a = null) /\ 0 <= (offset a) /\ (offset a) < (length a)),
  forall (caduceus5: Z),
  forall (Post10: caduceus5 = (acc intP a)),
  ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 267-303 *)
Lemma sort4bis_po_3 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (intP: ((memory) Z)),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (Pre7: ~(a = null) /\ 0 <= (offset a) /\ (offset a) < (length a)),
  forall (caduceus5: Z),
  forall (Post10: caduceus5 = (acc intP a)),
  forall (Pre6: ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b)),
  forall (aux_1: Z),
  forall (Post12: aux_1 = (acc intP b)),
  forall (result: bool),
  forall (Post14: (if result then caduceus5 > aux_1 else caduceus5 <= aux_1)),
  (if result
   then (forall (tmp:Z),
         (tmp = (acc intP a) ->
          (forall (result:Z),
           (result = (acc intP b) ->
            (forall (intP0:((memory) Z)),
             (intP0 = (upd intP a result) ->
              (forall (intP:((memory) Z)),
               (intP = (upd intP0 b tmp) -> (acc intP a) <= (acc intP b))) /\
              ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b))) /\
            ~(a = null) /\ 0 <= (offset a) /\ (offset a) < (length a))) /\
          ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b))) /\
   ~(a = null) /\ 0 <= (offset a) /\ (offset a) < (length a)
   else (acc intP a) <= (acc intP b)).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 553-568 *)
Lemma sort4bis_po_4 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 a) <= (acc intP0 b)),
  ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 601-616 *)
Lemma sort4bis_po_5 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 a) <= (acc intP0 b)),
  forall (Pre24: ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c)),
  forall (caduceus4: Z),
  forall (Post30: caduceus4 = (acc intP0 c)),
  ~(d = null) /\ 0 <= (offset d) /\ (offset d) < (length d).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 581-617 *)
Lemma sort4bis_po_6 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 a) <= (acc intP0 b)),
  forall (Pre24: ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c)),
  forall (caduceus4: Z),
  forall (Post30: caduceus4 = (acc intP0 c)),
  forall (Pre23: ~(d = null) /\ 0 <= (offset d) /\ (offset d) < (length d)),
  forall (aux_3: Z),
  forall (Post32: aux_3 = (acc intP0 d)),
  forall (result0: bool),
  forall (Post34: (if result0 then caduceus4 > aux_3 else caduceus4 <= aux_3)),
  (if result0
   then (forall (tmp:Z),
         (tmp = (acc intP0 c) ->
          (forall (result:Z),
           (result = (acc intP0 d) ->
            (forall (intP:((memory) Z)),
             (intP = (upd intP0 c result) ->
              (forall (intP0:((memory) Z)),
               (intP0 = (upd intP d tmp) -> (acc intP0 c) <= (acc intP0 d))) /\
              ~(d = null) /\ 0 <= (offset d) /\ (offset d) < (length d))) /\
            ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c))) /\
          ~(d = null) /\ 0 <= (offset d) /\ (offset d) < (length d))) /\
   ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c)
   else (acc intP0 c) <= (acc intP0 d)).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 877-892 *)
Lemma sort4bis_po_7 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 a) <= (acc intP0 b)),
  forall (intP1: ((memory) Z)),
  forall (Post29: (acc intP1 c) <= (acc intP1 d)),
  ~(a = null) /\ 0 <= (offset a) /\ (offset a) < (length a).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 926-941 *)
Lemma sort4bis_po_8 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 a) <= (acc intP0 b)),
  forall (intP1: ((memory) Z)),
  forall (Post29: (acc intP1 c) <= (acc intP1 d)),
  forall (Pre41: ~(a = null) /\ 0 <= (offset a) /\ (offset a) < (length a)),
  forall (caduceus3: Z),
  forall (Post50: caduceus3 = (acc intP1 a)),
  ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 906-942 *)
Lemma sort4bis_po_9 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 a) <= (acc intP0 b)),
  forall (intP1: ((memory) Z)),
  forall (Post29: (acc intP1 c) <= (acc intP1 d)),
  forall (Pre41: ~(a = null) /\ 0 <= (offset a) /\ (offset a) < (length a)),
  forall (caduceus3: Z),
  forall (Post50: caduceus3 = (acc intP1 a)),
  forall (Pre40: ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c)),
  forall (aux_5: Z),
  forall (Post52: aux_5 = (acc intP1 c)),
  forall (result1: bool),
  forall (Post54: (if result1 then caduceus3 > aux_5 else caduceus3 <= aux_5)),
  (if result1
   then (forall (tmp:Z),
         (tmp = (acc intP1 a) ->
          (forall (result:Z),
           (result = (acc intP1 c) ->
            (forall (intP:((memory) Z)),
             (intP = (upd intP1 a result) ->
              (forall (intP0:((memory) Z)),
               (intP0 = (upd intP c tmp) -> (acc intP0 a) <= (acc intP0 c))) /\
              ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c))) /\
            ~(a = null) /\ 0 <= (offset a) /\ (offset a) < (length a))) /\
          ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c))) /\
   ~(a = null) /\ 0 <= (offset a) /\ (offset a) < (length a)
   else (acc intP1 a) <= (acc intP1 c)).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 1230-1245 *)
Lemma sort4bis_po_10 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 a) <= (acc intP0 b)),
  forall (intP1: ((memory) Z)),
  forall (Post29: (acc intP1 c) <= (acc intP1 d)),
  forall (intP2: ((memory) Z)),
  forall (Post49: (acc intP2 a) <= (acc intP2 c)),
  ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 1280-1295 *)
Lemma sort4bis_po_11 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 a) <= (acc intP0 b)),
  forall (intP1: ((memory) Z)),
  forall (Post29: (acc intP1 c) <= (acc intP1 d)),
  forall (intP2: ((memory) Z)),
  forall (Post49: (acc intP2 a) <= (acc intP2 c)),
  forall (Pre58: ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b)),
  forall (caduceus2: Z),
  forall (Post70: caduceus2 = (acc intP2 b)),
  ~(d = null) /\ 0 <= (offset d) /\ (offset d) < (length d).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 1260-1296 *)
Lemma sort4bis_po_12 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 a) <= (acc intP0 b)),
  forall (intP1: ((memory) Z)),
  forall (Post29: (acc intP1 c) <= (acc intP1 d)),
  forall (intP2: ((memory) Z)),
  forall (Post49: (acc intP2 a) <= (acc intP2 c)),
  forall (Pre58: ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b)),
  forall (caduceus2: Z),
  forall (Post70: caduceus2 = (acc intP2 b)),
  forall (Pre57: ~(d = null) /\ 0 <= (offset d) /\ (offset d) < (length d)),
  forall (aux_7: Z),
  forall (Post72: aux_7 = (acc intP2 d)),
  forall (result2: bool),
  forall (Post74: (if result2 then caduceus2 > aux_7 else caduceus2 <= aux_7)),
  (if result2
   then (forall (tmp:Z),
         (tmp = (acc intP2 b) ->
          (forall (result:Z),
           (result = (acc intP2 d) ->
            (forall (intP:((memory) Z)),
             (intP = (upd intP2 b result) ->
              (forall (intP0:((memory) Z)),
               (intP0 = (upd intP d tmp) -> (acc intP0 b) <= (acc intP0 d))) /\
              ~(d = null) /\ 0 <= (offset d) /\ (offset d) < (length d))) /\
            ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b))) /\
          ~(d = null) /\ 0 <= (offset d) /\ (offset d) < (length d))) /\
   ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b)
   else (acc intP2 b) <= (acc intP2 d)).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 1580-1595 *)
Lemma sort4bis_po_13 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 a) <= (acc intP0 b)),
  forall (intP1: ((memory) Z)),
  forall (Post29: (acc intP1 c) <= (acc intP1 d)),
  forall (intP2: ((memory) Z)),
  forall (Post49: (acc intP2 a) <= (acc intP2 c)),
  forall (intP3: ((memory) Z)),
  forall (Post69: (acc intP3 b) <= (acc intP3 d)),
  ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 1629-1644 *)
Lemma sort4bis_po_14 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 a) <= (acc intP0 b)),
  forall (intP1: ((memory) Z)),
  forall (Post29: (acc intP1 c) <= (acc intP1 d)),
  forall (intP2: ((memory) Z)),
  forall (Post49: (acc intP2 a) <= (acc intP2 c)),
  forall (intP3: ((memory) Z)),
  forall (Post69: (acc intP3 b) <= (acc intP3 d)),
  forall (Pre75: ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b)),
  forall (caduceus1: Z),
  forall (Post89: caduceus1 = (acc intP3 b)),
  ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "sort.why", characters 1609-1645 *)
Lemma sort4bis_po_15 : 
  forall (a: pointer),
  forall (b: pointer),
  forall (c: pointer),
  forall (d: pointer),
  forall (Pre86: (((valid a) /\ (valid b)) /\ (valid c)) /\ (valid d)),
  forall (tmp: Z),
  forall (Post1: tmp = (any_int tt)),
  forall (intP0: ((memory) Z)),
  forall (Post9: (acc intP0 a) <= (acc intP0 b)),
  forall (intP1: ((memory) Z)),
  forall (Post29: (acc intP1 c) <= (acc intP1 d)),
  forall (intP2: ((memory) Z)),
  forall (Post49: (acc intP2 a) <= (acc intP2 c)),
  forall (intP3: ((memory) Z)),
  forall (Post69: (acc intP3 b) <= (acc intP3 d)),
  forall (Pre75: ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b)),
  forall (caduceus1: Z),
  forall (Post89: caduceus1 = (acc intP3 b)),
  forall (Pre74: ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c)),
  forall (aux_9: Z),
  forall (Post91: aux_9 = (acc intP3 c)),
  forall (result3: bool),
  forall (Post93: (if result3 then caduceus1 > aux_9 else caduceus1 <= aux_9)),
  (if result3
   then (forall (tmp:Z),
         (tmp = (acc intP3 b) ->
          (forall (result:Z),
           (result = (acc intP3 c) ->
            (forall (intP:((memory) Z)),
             (intP = (upd intP3 b result) ->
              (forall (intP0:((memory) Z)),
               (intP0 = (upd intP c tmp) -> (acc intP0 b) <= (acc intP0 c))) /\
              ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c))) /\
            ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b))) /\
          ~(c = null) /\ 0 <= (offset c) /\ (offset c) < (length c))) /\
   ~(b = null) /\ 0 <= (offset b) /\ (offset b) < (length b)
   else (acc intP3 b) <= (acc intP3 c)).
Proof.
(* FILL PROOF HERE *)
Save.

