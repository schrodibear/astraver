
Require WhyArrays.
Require WhyPermut.

(* A tactic to simplify access in arrays *)

Tactic Definition WhyArrays :=
  Repeat Rewrite store_def_1;
  Repeat Rewrite array_length_store.

Tactic Definition WhyAccessStore i j H :=
  Elim (Z_eq_dec i j); [ 
    Intro H; Rewrite H; Rewrite store_def_1; WhyArrays
  | Intro H; Rewrite store_def_2; 
             [ Idtac | Idtac | Idtac | Exact H ] ].

Tactic Definition CallSubst x := Subst x.

Tactic Definition WhyBounds :=
  Omega Orelse 
  Match Context With
  | [ h: (exchange ?1 ?2 ?3 ?4) |- ? ] ->
    Generalize (exchange_length ?1 ?2 ?3 ?4 h); Intro Hel; WhyBounds
  | [ |- (Zle `0` ?) /\ (Zlt ? (array_length ?1)) ] -> 
    Try (CallSubst ?1; Simpl; Omega)
  | _ -> 
    Idtac.

Tactic Definition WhyStoreOther :=
  Rewrite store_def_2; WhyArrays; WhyBounds.

Tactic Definition WhyLength t :=
  Subst t; Simpl; Try Omega.

