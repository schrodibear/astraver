(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)
Require Export jessie_why.

(*Why type*) Definition Object: Set.
Admitted.

(*Why type*) Definition interface: Set.
Admitted.

(*Why logic*) Definition Exception_tag : (tag_id Object).
Admitted.

(*Why logic*) Definition Object_tag : (tag_id Object).
Admitted.

(*Why axiom*) Lemma Exception_parenttag_Object :
  (parenttag Exception_tag Object_tag).
Admitted.

(*Why logic*) Definition Fibonacci_tag : (tag_id Object).
Admitted.

(*Why axiom*) Lemma Fibonacci_parenttag_Object :
  (parenttag Fibonacci_tag Object_tag).
Admitted.

(*Why predicate*) Definition Non_null_Object  (x:(pointer Object)) (Object_alloc_table:(alloc_table Object))
  := (offset_max Object_alloc_table x) = 0.

(*Why axiom*) Lemma Object_int : (int_of_tag Object_tag) = 1.
Admitted.

(*Why logic*) Definition Object_of_pointer_address :
  (pointer unit) -> (pointer Object).
Admitted.

(*Why axiom*) Lemma Object_of_pointer_address_of_pointer_addr :
  (forall (p:(pointer Object)),
   p = (Object_of_pointer_address (pointer_address p))).
Admitted.

(*Why axiom*) Lemma Object_parenttag_bottom :
  (parenttag Object_tag (@bottom_tag Object)).
Admitted.

(*Why axiom*) Lemma Object_tags :
  (forall (x:(pointer Object)),
   (forall (Object_tag_table:(tag_table Object)),
    (instanceof Object_tag_table x Object_tag))).
Admitted.

(*Why logic*) Definition String_tag : (tag_id Object).
Admitted.

(*Why axiom*) Lemma String_parenttag_Object :
  (parenttag String_tag Object_tag).
Admitted.

(*Why logic*) Definition Throwable_tag : (tag_id Object).
Admitted.

(*Why axiom*) Lemma Throwable_parenttag_Object :
  (parenttag Throwable_tag Object_tag).
Admitted.


(*Why logic*) Definition interface_tag : (tag_id interface).
Admitted.

(*Why axiom*) Lemma interface_int : (int_of_tag interface_tag) = 1.
Admitted.

(*Why logic*) Definition interface_of_pointer_address :
  (pointer unit) -> (pointer interface).
Admitted.

(*Why axiom*) Lemma interface_of_pointer_address_of_pointer_addr :
  (forall (p:(pointer interface)),
   p = (interface_of_pointer_address (pointer_address p))).
Admitted.

(*Why axiom*) Lemma interface_parenttag_bottom :
  (parenttag interface_tag (@bottom_tag interface)).
Admitted.

(*Why axiom*) Lemma interface_tags :
  (forall (x:(pointer interface)),
   (forall (interface_tag_table:(tag_table interface)),
    (instanceof interface_tag_table x interface_tag))).
Admitted.

(*Why inductive*) Inductive isfib  : Z -> Z -> Prop 
  := | isfib0 : (isfib 0 0)
     
     | isfib1 : (isfib 1 1)
     
     | isfibn : (forall (n:Z),
                 (forall (r_0:Z),
                  (forall (p:Z),
                   (n >= 2 /\ (isfib (n - 2) r_0) /\ (isfib (n - 1) p) ->
                    (isfib n (p + r_0))))))
     .

(* Why obligation from file "Fibonacci.jc", line 57, characters 0-29: *)
(*Why goal*) Lemma isfib_2_1 : 
  (isfib 2 1).
Proof.
apply isfibn with (r_0:=0) (p:=1); intuition.
apply isfib0.
apply isfib1.
Save.

(*Why axiom*) Lemma isfib_2_1_as_axiom : (isfib 2 1).
Admitted.

(* Why obligation from file "Fibonacci.jc", line 51, characters 0-29: *)
(*Why goal*) Lemma isfib_6_8 : 
  (isfib 6 8).
Proof.
assert (isfib3: isfib 3 2).
apply isfibn with (r_0:=1) (p:=1); intuition.
apply isfib1.
apply isfib_2_1.
assert (isfib4: isfib 4 3).
apply isfibn with (r_0:=1) (p:=2); intuition.
apply isfib_2_1.
assert (isfib5: isfib 5 5).
apply isfibn with (r_0:=2) (p:=3); intuition.
apply isfibn with (r_0:=3) (p:=5); intuition.
Qed.



(*Why axiom*) Lemma isfib_6_8_as_axiom : (isfib 6 8).
Admitted.

(*Why predicate*) Definition left_valid_struct_Object  (p:(pointer Object)) (a:Z) (Object_alloc_table:(alloc_table Object))
  := (offset_min Object_alloc_table p) <= a.

(*Why predicate*) Definition left_valid_struct_Exception  (p:(pointer Object)) (a:Z) (Object_alloc_table:(alloc_table Object))
  := (left_valid_struct_Object p a Object_alloc_table).

(*Why predicate*) Definition left_valid_struct_Fibonacci  (p:(pointer Object)) (a:Z) (Object_alloc_table:(alloc_table Object))
  := (left_valid_struct_Object p a Object_alloc_table).

(*Why predicate*) Definition left_valid_struct_String  (p:(pointer Object)) (a:Z) (Object_alloc_table:(alloc_table Object))
  := (left_valid_struct_Object p a Object_alloc_table).

(*Why predicate*) Definition left_valid_struct_Throwable  (p:(pointer Object)) (a:Z) (Object_alloc_table:(alloc_table Object))
  := (left_valid_struct_Object p a Object_alloc_table).

(*Why predicate*) Definition left_valid_struct_interface  (p:(pointer interface)) (a:Z) (interface_alloc_table:(alloc_table interface))
  := (offset_min interface_alloc_table p) <= a.

(* Why obligation from file "Fibonacci.jc", line 54, characters 0-37: *)
(*Why goal*) Lemma not_isfib_2_2 : 
  ~(isfib 2 2).
Proof.
intro h; inversion h; intuition.
replace (p + r_0 - (p + r_0)) with 0 in H1 by omega.
inversion H1; auto with zarith.
assert (p=2) by omega.
subst.
replace (2 + 0 - 1) with 1 in H4 by omega.
inversion H4; auto with zarith.
Save.


(*Why axiom*) Lemma not_isfib_2_2_as_axiom : ~(isfib 2 2).
Admitted.

(*Why axiom*) Lemma pointer_addr_of_Object_of_pointer_address :
  (forall (p:(pointer unit)),
   p = (pointer_address (Object_of_pointer_address p))).
Admitted.

(*Why axiom*) Lemma pointer_addr_of_interface_of_pointer_address :
  (forall (p:(pointer unit)),
   p = (pointer_address (interface_of_pointer_address p))).
Admitted.

(*Why predicate*) Definition right_valid_struct_Object  (p:(pointer Object)) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (offset_max Object_alloc_table p) >= b.

(*Why predicate*) Definition right_valid_struct_Exception  (p:(pointer Object)) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (right_valid_struct_Object p b Object_alloc_table).

(*Why predicate*) Definition right_valid_struct_Fibonacci  (p:(pointer Object)) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (right_valid_struct_Object p b Object_alloc_table).

(*Why predicate*) Definition right_valid_struct_String  (p:(pointer Object)) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (right_valid_struct_Object p b Object_alloc_table).

(*Why predicate*) Definition right_valid_struct_Throwable  (p:(pointer Object)) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (right_valid_struct_Object p b Object_alloc_table).

(*Why predicate*) Definition right_valid_struct_interface  (p:(pointer interface)) (b:Z) (interface_alloc_table:(alloc_table interface))
  := (offset_max interface_alloc_table p) >= b.

(*Why predicate*) Definition strict_valid_root_Object  (p:(pointer Object)) (a:Z) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (offset_min Object_alloc_table p) = a /\
     (offset_max Object_alloc_table p) = b.

(*Why predicate*) Definition strict_valid_root_interface  (p:(pointer interface)) (a:Z) (b:Z) (interface_alloc_table:(alloc_table interface))
  := (offset_min interface_alloc_table p) = a /\
     (offset_max interface_alloc_table p) = b.

(*Why predicate*) Definition strict_valid_struct_Object  (p:(pointer Object)) (a:Z) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (offset_min Object_alloc_table p) = a /\
     (offset_max Object_alloc_table p) = b.

(*Why predicate*) Definition strict_valid_struct_Exception  (p:(pointer Object)) (a:Z) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (strict_valid_struct_Object p a b Object_alloc_table).

(*Why predicate*) Definition strict_valid_struct_Fibonacci  (p:(pointer Object)) (a:Z) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (strict_valid_struct_Object p a b Object_alloc_table).

(*Why predicate*) Definition strict_valid_struct_String  (p:(pointer Object)) (a:Z) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (strict_valid_struct_Object p a b Object_alloc_table).

(*Why predicate*) Definition strict_valid_struct_Throwable  (p:(pointer Object)) (a:Z) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (strict_valid_struct_Object p a b Object_alloc_table).

(*Why predicate*) Definition strict_valid_struct_interface  (p:(pointer interface)) (a:Z) (b:Z) (interface_alloc_table:(alloc_table interface))
  := (offset_min interface_alloc_table p) = a /\
     (offset_max interface_alloc_table p) = b.

(*Why predicate*) Definition valid_bitvector_struct_Object  (p:(pointer unit)) (a:Z) (b:Z) (bitvector_alloc_table:(alloc_table unit))
  := (offset_min bitvector_alloc_table p) = a /\
     (offset_max bitvector_alloc_table p) = b.

(*Why predicate*) Definition valid_bitvector_struct_Exception  (p:(pointer unit)) (a:Z) (b:Z) (bitvector_alloc_table:(alloc_table unit))
  := (valid_bitvector_struct_Object p a b bitvector_alloc_table).

(*Why predicate*) Definition valid_bitvector_struct_Fibonacci  (p:(pointer unit)) (a:Z) (b:Z) (bitvector_alloc_table:(alloc_table unit))
  := (valid_bitvector_struct_Object p a b bitvector_alloc_table).

(*Why predicate*) Definition valid_bitvector_struct_String  (p:(pointer unit)) (a:Z) (b:Z) (bitvector_alloc_table:(alloc_table unit))
  := (valid_bitvector_struct_Object p a b bitvector_alloc_table).

(*Why predicate*) Definition valid_bitvector_struct_Throwable  (p:(pointer unit)) (a:Z) (b:Z) (bitvector_alloc_table:(alloc_table unit))
  := (valid_bitvector_struct_Object p a b bitvector_alloc_table).

(*Why predicate*) Definition valid_bitvector_struct_interface  (p:(pointer unit)) (a:Z) (b:Z) (bitvector_alloc_table:(alloc_table unit))
  := (offset_min bitvector_alloc_table p) = a /\
     (offset_max bitvector_alloc_table p) = b.

(*Why predicate*) Definition valid_root_Object  (p:(pointer Object)) (a:Z) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (offset_min Object_alloc_table p) <= a /\
     (offset_max Object_alloc_table p) >= b.

(*Why predicate*) Definition valid_root_interface  (p:(pointer interface)) (a:Z) (b:Z) (interface_alloc_table:(alloc_table interface))
  := (offset_min interface_alloc_table p) <= a /\
     (offset_max interface_alloc_table p) >= b.

(*Why predicate*) Definition valid_struct_Object  (p:(pointer Object)) (a:Z) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (offset_min Object_alloc_table p) <= a /\
     (offset_max Object_alloc_table p) >= b.

(*Why predicate*) Definition valid_struct_Exception  (p:(pointer Object)) (a:Z) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (valid_struct_Object p a b Object_alloc_table).

(*Why predicate*) Definition valid_struct_Fibonacci  (p:(pointer Object)) (a:Z) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (valid_struct_Object p a b Object_alloc_table).

(*Why predicate*) Definition valid_struct_String  (p:(pointer Object)) (a:Z) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (valid_struct_Object p a b Object_alloc_table).

(*Why predicate*) Definition valid_struct_Throwable  (p:(pointer Object)) (a:Z) (b:Z) (Object_alloc_table:(alloc_table Object))
  := (valid_struct_Object p a b Object_alloc_table).

(*Why predicate*) Definition valid_struct_interface  (p:(pointer interface)) (a:Z) (b:Z) (interface_alloc_table:(alloc_table interface))
  := (offset_min interface_alloc_table p) <= a /\
     (offset_max interface_alloc_table p) >= b.

(* Why obligation from file "Fibonacci.java", line 29, characters 20-26: *)
(*Why goal*) Lemma Fibonacci_Fib_ensures_default_po_1 : 
  forall (n_0: Z),
  forall (HW_1: (* JC_13 *) n_0 >= 0),
  (* JC_32 *) (* JC_28 *) (* JC_28 *) 0 <= 0.
Proof.
intuition.
Save.

(* Why obligation from file "Fibonacci.java", line 29, characters 25-31: *)
(*Why goal*) Lemma Fibonacci_Fib_ensures_default_po_2 : 
  forall (n_0: Z),
  forall (HW_1: (* JC_13 *) n_0 >= 0),
  (* JC_32 *) (* JC_29 *) (* JC_29 *) 0 <= n_0.
Proof.
intuition.
Save.

(* Why obligation from file "Fibonacci.java", line 29, characters 35-47: *)
(*Why goal*) Lemma Fibonacci_Fib_ensures_default_po_3 : 
  forall (n_0: Z),
  forall (HW_1: (* JC_13 *) n_0 >= 0),
  (* JC_32 *) (* JC_30 *) (* JC_30 *) (isfib (0 + 1) 1).
Proof.
intros; apply isfib1.
Save.

(* Why obligation from file "Fibonacci.java", line 29, characters 51-61: *)
(*Why goal*) Lemma Fibonacci_Fib_ensures_default_po_4 : 
  forall (n_0: Z),
  forall (HW_1: (* JC_13 *) n_0 >= 0),
  (* JC_32 *) (* JC_31 *) (* JC_31 *) (isfib 0 0).
Proof.
intros; apply isfib0.
Save.

(* Why obligation from file "Fibonacci.java", line 29, characters 20-26: *)
(*Why goal*) Lemma Fibonacci_Fib_ensures_default_po_5 : 
  forall (n_0: Z),
  forall (HW_1: (* JC_13 *) n_0 >= 0),
  forall (i: Z),
  forall (x_0_0: Z),
  forall (y: Z),
  forall (HW_4: (* JC_32 *) ((* JC_28 *) 0 <= i /\ (* JC_29 *) i <= n_0 /\
                (* JC_30 *) (isfib (i + 1) x_0_0) /\ (* JC_31 *) (isfib i y))),
  forall (HW_6: i < n_0),
  forall (aux: Z),
  forall (HW_7: aux = y),
  forall (y0: Z),
  forall (HW_8: y0 = x_0_0),
  forall (x_0_0_0: Z),
  forall (HW_9: x_0_0_0 = (x_0_0 + aux)),
  forall (i0: Z),
  forall (HW_10: i0 = (i + 1)),
  (* JC_32 *) (* JC_28 *) (* JC_28 *) 0 <= i0.
Proof.
intuition.
Save.

(* Why obligation from file "Fibonacci.java", line 29, characters 25-31: *)
(*Why goal*) Lemma Fibonacci_Fib_ensures_default_po_6 : 
  forall (n_0: Z),
  forall (HW_1: (* JC_13 *) n_0 >= 0),
  forall (i: Z),
  forall (x_0_0: Z),
  forall (y: Z),
  forall (HW_4: (* JC_32 *) ((* JC_28 *) 0 <= i /\ (* JC_29 *) i <= n_0 /\
                (* JC_30 *) (isfib (i + 1) x_0_0) /\ (* JC_31 *) (isfib i y))),
  forall (HW_6: i < n_0),
  forall (aux: Z),
  forall (HW_7: aux = y),
  forall (y0: Z),
  forall (HW_8: y0 = x_0_0),
  forall (x_0_0_0: Z),
  forall (HW_9: x_0_0_0 = (x_0_0 + aux)),
  forall (i0: Z),
  forall (HW_10: i0 = (i + 1)),
  (* JC_32 *) (* JC_29 *) (* JC_29 *) i0 <= n_0.
Proof.
intuition.
Save.

(* Why obligation from file "Fibonacci.java", line 29, characters 35-47: *)
(*Why goal*) Lemma Fibonacci_Fib_ensures_default_po_7 : 
  forall (n_0: Z),
  forall (HW_1: (* JC_13 *) n_0 >= 0),
  forall (i: Z),
  forall (x_0_0: Z),
  forall (y: Z),
  forall (HW_4: (* JC_32 *) ((* JC_28 *) 0 <= i /\ (* JC_29 *) i <= n_0 /\
                (* JC_30 *) (isfib (i + 1) x_0_0) /\ (* JC_31 *) (isfib i y))),
  forall (HW_6: i < n_0),
  forall (aux: Z),
  forall (HW_7: aux = y),
  forall (y0: Z),
  forall (HW_8: y0 = x_0_0),
  forall (x_0_0_0: Z),
  forall (HW_9: x_0_0_0 = (x_0_0 + aux)),
  forall (i0: Z),
  forall (HW_10: i0 = (i + 1)),
  (* JC_32 *) (* JC_30 *) (* JC_30 *) (isfib (i0 + 1) x_0_0_0).
Proof.
intuition;subst; auto.
apply isfibn; intuition.
replace (i+1+1-2) with i; auto with zarith.
replace (i+1+1-1) with (i+1); auto with zarith.
Save.

(* Why obligation from file "Fibonacci.java", line 29, characters 51-61: *)
(*Why goal*) Lemma Fibonacci_Fib_ensures_default_po_8 : 
  forall (n_0: Z),
  forall (HW_1: (* JC_13 *) n_0 >= 0),
  forall (i: Z),
  forall (x_0_0: Z),
  forall (y: Z),
  forall (HW_4: (* JC_32 *) ((* JC_28 *) 0 <= i /\ (* JC_29 *) i <= n_0 /\
                (* JC_30 *) (isfib (i + 1) x_0_0) /\ (* JC_31 *) (isfib i y))),
  forall (HW_6: i < n_0),
  forall (aux: Z),
  forall (HW_7: aux = y),
  forall (y0: Z),
  forall (HW_8: y0 = x_0_0),
  forall (x_0_0_0: Z),
  forall (HW_9: x_0_0_0 = (x_0_0 + aux)),
  forall (i0: Z),
  forall (HW_10: i0 = (i + 1)),
  (* JC_32 *) (* JC_31 *) (* JC_31 *) (isfib i0 y0).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "Fibonacci.java", line 24, characters 16-33: *)
(*Why goal*) Lemma Fibonacci_Fib_ensures_default_po_9 : 
  forall (n_0: Z),
  forall (HW_1: (* JC_13 *) n_0 >= 0),
  forall (i: Z),
  forall (x_0_0: Z),
  forall (y: Z),
  forall (HW_4: (* JC_32 *) ((* JC_28 *) 0 <= i /\ (* JC_29 *) i <= n_0 /\
                (* JC_30 *) (isfib (i + 1) x_0_0) /\ (* JC_31 *) (isfib i y))),
  forall (HW_11: i >= n_0),
  forall (why__return: Z),
  forall (HW_12: why__return = y),
  (* JC_15 *) (isfib n_0 why__return).
Proof.
intuition.
assert (i=n_0) by omega.
subst; auto.
Save.

(* Why obligation from file "Fibonacci.java", line 30, characters 18-21: *)
(*Why goal*) Lemma Fibonacci_Fib_safety_po_1 : 
  forall (n_0: Z),
  forall (HW_1: (* JC_13 *) n_0 >= 0),
  forall (i: Z),
  forall (x_0_0: Z),
  forall (y: Z),
  forall (HW_4: (* JC_25 *) True),
  forall (HW_5: (* JC_23 *) ((* JC_19 *) 0 <= i /\ (* JC_20 *) i <= n_0 /\
                (* JC_21 *) (isfib (i + 1) x_0_0) /\ (* JC_22 *) (isfib i y))),
  forall (HW_6: i < n_0),
  forall (aux: Z),
  forall (HW_7: aux = y),
  forall (y0: Z),
  forall (HW_8: y0 = x_0_0),
  forall (x_0_0_0: Z),
  forall (HW_9: x_0_0_0 = (x_0_0 + aux)),
  forall (i0: Z),
  forall (HW_10: i0 = (i + 1)),
  0 <= ((* JC_27 *) (n_0 - i)).
Proof.
intuition.
Save.

(* Why obligation from file "Fibonacci.java", line 30, characters 18-21: *)
(*Why goal*) Lemma Fibonacci_Fib_safety_po_2 : 
  forall (n_0: Z),
  forall (HW_1: (* JC_13 *) n_0 >= 0),
  forall (i: Z),
  forall (x_0_0: Z),
  forall (y: Z),
  forall (HW_4: (* JC_25 *) True),
  forall (HW_5: (* JC_23 *) ((* JC_19 *) 0 <= i /\ (* JC_20 *) i <= n_0 /\
                (* JC_21 *) (isfib (i + 1) x_0_0) /\ (* JC_22 *) (isfib i y))),
  forall (HW_6: i < n_0),
  forall (aux: Z),
  forall (HW_7: aux = y),
  forall (y0: Z),
  forall (HW_8: y0 = x_0_0),
  forall (x_0_0_0: Z),
  forall (HW_9: x_0_0_0 = (x_0_0 + aux)),
  forall (i0: Z),
  forall (HW_10: i0 = (i + 1)),
  ((* JC_27 *) (n_0 - i0)) < ((* JC_27 *) (n_0 - i)).
Proof.
intuition.
Save.

