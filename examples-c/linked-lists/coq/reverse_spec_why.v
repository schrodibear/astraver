(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Caduceus.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

Admitted.

(*Why type*) Definition global: Set.
Admitted.

(*Why type*) Definition plist: Set.
exact (plist Z23).
Defined.

(*Why type*) Definition Length: Set.
exact (Length Z23).
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
  (forall (alloc:alloc_table),
   (* File "list.h", line 50, characters 6-124 *)
   (forall (p1:((pointer) global)),
    (forall (l:plist),
     (forall (p2:((pointer) global)),
      ((valid alloc p1) /\
       (lpath tl_global alloc (acc tl_global p1) l p2) <->
       (lpath tl_global alloc p1 (cons p1 l) p2)))))).
Admitted.

(*Why logic*) Definition nil : plist.
exact nil.
Defined.

(*Why axiom*) Lemma Path_null_ax :
  (forall (alloc:alloc_table),
   (* File "list.h", line 44, characters 26-58 *)
   (forall (p:((pointer) global)), (lpath tl_global alloc p nil p))).
Admitted.

(*Why axiom*) Lemma Path_null_inv_ax :
  (forall (alloc:alloc_table),
   (* File "list.h", line 47, characters 6-63 *)
   (forall (p:((pointer) global)),
    (forall (l:plist), ((lpath tl_global alloc p l p) -> l = nil)))).
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
  := (* File "list.h", line 61, characters 40-56 *)
     (lpath tl_global alloc p l null).

(*Why predicate*) Definition is_list  (tl_global:((memory) ((pointer) global)
  global)) (alloc:alloc_table) (l:((pointer) global))
  := (* File "list.h", line 63, characters 33-63 *)
     (exists pl:plist, (llist tl_global alloc l pl)).

(*Why axiom*) Lemma is_list_llist_ax :
  (forall (alloc:alloc_table),
   (* File "list.h", line 66, characters 6-64 *)
   (forall (p:((pointer) global)),
    ((is_list tl_global alloc p) <->
     (exists l:plist, (llist tl_global alloc p l))))).
Admitted.

(*Why logic*) Definition length :
  alloc_table -> ((pointer) global) -> Length.
Admitted.

(*Why logic*) Definition list_length : plist -> Z.
Admitted.

(*Why axiom*) Lemma llist_function_ax :
  (forall (alloc:alloc_table),
   (* File "list.h", line 69, characters 6-99 *)
   (forall (l1:plist),
    (forall (l2:plist),
     (forall (p:((pointer) global)),
      ((llist tl_global alloc p l1) ->
       ((llist tl_global alloc p l2) -> l1 = l2)))))).
Admitted.

(*Why axiom*) Lemma llist_valid :
  (forall (alloc:alloc_table),
   (* File "list.h", line 73, characters 6-85 *)
   (forall (p1:((pointer) global)),
    (forall (l:plist),
     ((llist tl_global alloc p1 l) -> (~(p1 = null) -> (valid alloc p1)))))).
Admitted.

(*Why logic*) Definition rev : plist -> plist.
Admitted.

(*Why axiom*) Lemma rev_nil_ax :
  (* File "list.h", line 23, characters 24-43 *) (rev nil) = nil.
Admitted.

