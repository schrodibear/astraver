(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Caduceus.

(*Why type*) Definition global: Set.
Admitted.

(*Why type*) Definition plist: Set.
exact (plist global).
Defined.

(*Why type*) Definition Length: Set.
exact (Length global).
Defined.

(*Why logic*) Definition lpath :
  ((memory) ((pointer) global) global) -> alloc_table -> ((pointer) global)
  -> plist -> ((pointer) global) -> Prop.
exact (fun m a => lpath _ a (acc m)).
Defined.

(*Why logic*) Definition cons : ((pointer) global) -> plist -> plist.
exact (fun p => cons p).
Defined.

(*Why axiom*) Lemma Path_cons_inv :
  (forall (tl_global:((memory) ((pointer) global) global)),
   (forall (alloc:alloc_table),
    (* File "list.h", line 52, characters 6-124 *)
    (forall (p1:((pointer) global)),
     (forall (l:plist),
      (forall (p2:((pointer) global)),
       ((valid alloc p1) /\
        (lpath tl_global alloc (acc tl_global p1) l p2) <->
        (lpath tl_global alloc p1 (cons p1 l) p2))))))).
Admitted.

(*Why logic*) Definition nil : plist.
exact nil.
Defined.

(*Why axiom*) Lemma Path_null_ax :
  (forall (tl_global:((memory) ((pointer) global) global)),
   (forall (alloc:alloc_table),
    (* File "list.h", line 46, characters 26-58 *)
    (forall (p:((pointer) global)), (lpath tl_global alloc p nil p)))).
Admitted.

(*Why axiom*) Lemma Path_null_inv_ax :
  (forall (tl_global:((memory) ((pointer) global) global)),
   (forall (alloc:alloc_table),
    (* File "list.h", line 49, characters 6-63 *)
    (forall (p:((pointer) global)),
     (forall (l:plist), ((lpath tl_global alloc p l p) -> l = nil))))).
Admitted.

(*Why logic*) Definition app : plist -> plist -> plist.
exact (fun p => app p).
Defined.

(*Why axiom*) Lemma app_nil_1_ax :
  (* File "list.h", line 25, characters 26-60 *)
  (forall (l:plist), l = (app l nil)).
Admitted.

(*Why axiom*) Lemma app_nil_2_ax :
  (* File "list.h", line 27, characters 26-60 *)
  (forall (l:plist), l = (app nil l)).
Admitted.

(*Why logic*) Definition cyclic :
  ((memory) ((pointer) global) global) -> alloc_table
  -> ((pointer) global) -> Prop.
Admitted.

(*Why logic*) Definition disjoint : plist -> plist -> Prop.
exact (fun p => disjoint p).
Defined.

(*Why axiom*) Lemma disjoint_nil1 :
  (* File "list.h", line 29, characters 27-61 *)
  (forall (l:plist), (disjoint l nil)).
Admitted.

(*Why axiom*) Lemma disjoint_nil2 :
  (* File "list.h", line 31, characters 27-61 *)
  (forall (l:plist), (disjoint nil l)).
Admitted.

(*Why logic*) Definition finite :
  ((memory) ((pointer) global) global) -> alloc_table
  -> ((pointer) global) -> Prop.
Admitted.

(*Why predicate*) Definition llist  (tl_global:((memory) ((pointer) global)
  global)) (alloc:alloc_table) (p:((pointer) global)) (l:plist)
  := (* File "list.h", line 63, characters 40-56 *)
     (lpath tl_global alloc p l null).

(*Why predicate*) Definition is_list  (tl_global:((memory) ((pointer) global)
  global)) (alloc:alloc_table) (l:((pointer) global))
  := (* File "list.h", line 65, characters 33-63 *)
     (exists pl:plist, (llist tl_global alloc l pl)).

(*Why axiom*) Lemma is_list_llist_ax :
  (forall (tl_global:((memory) ((pointer) global) global)),
   (forall (alloc:alloc_table),
    (* File "list.h", line 68, characters 6-64 *)
    (forall (p:((pointer) global)),
     ((is_list tl_global alloc p) <->
      (exists l:plist, (llist tl_global alloc p l)))))).
Admitted.

(*Why logic*) Definition length :
  ((memory) ((pointer) global) global) -> alloc_table
  -> ((pointer) global) -> Length.
exact (fun tl a p => length global a tl p). 
Defined.

(*Why logic*) Definition length_order : Length -> Length -> Prop.
exact (length_order global).
Defined.

(*Why logic*) Definition list_length : plist -> Z.
exact (fun l => Z_of_nat (List.length l)).
Defined.

(*Why axiom*) Lemma llist_function_ax :
  (forall (tl_global:((memory) ((pointer) global) global)),
   (forall (alloc:alloc_table),
    (* File "list.h", line 71, characters 6-99 *)
    (forall (l1:plist),
     (forall (l2:plist),
      (forall (p:((pointer) global)),
       ((llist tl_global alloc p l1) ->
        ((llist tl_global alloc p l2) -> l1 = l2))))))).
Admitted.

(*Why axiom*) Lemma llist_valid :
  (forall (tl_global:((memory) ((pointer) global) global)),
   (forall (alloc:alloc_table),
    (* File "list.h", line 75, characters 6-85 *)
    (forall (p1:((pointer) global)),
     (forall (l:plist),
      ((llist tl_global alloc p1 l) -> (~(p1 = null) -> (valid alloc p1))))))).
Admitted.

(*Why logic*) Definition rev : plist -> plist.
exact (fun l => rev l).
Defined.

(*Why axiom*) Lemma rev_nil_ax :
  (* File "list.h", line 23, characters 24-43 *) (rev nil) = nil.
Admitted.

