(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export latespec_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (A723:Set),
  forall (p: ((pointer) A723)),
  forall (alloc: alloc_table),
  forall (intM_p_5: ((memory) Z A723)),
  forall (HW_1: (* File "latespec.c", line 7, characters 14-23 *)
                (valid alloc p)),
  forall (HW_2: (valid alloc p)),
  forall (intM_p_5_0: ((memory) Z A723)),
  forall (HW_3: intM_p_5_0 = (upd intM_p_5 p 0)),
  (not_assigns alloc intM_p_5 intM_p_5_0 (pset_singleton p)).
Proof.
intuition.
red;intros.
subst;auto.
rewrite acc_upd_neq;auto.
assert (p0<>p).
apply pset_singleton_elim;auto.
auto.
Save.

