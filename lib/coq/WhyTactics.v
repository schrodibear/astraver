
Require WhyArrays.
Require WhyPermut.

Tactic Definition CallSubst x := Subst x.

Tactic Definition WhyBounds :=
  Omega Orelse 
  Match Context With
  | [ h: (exchange ? ? ? ?) |- ? ] ->
    Generalize (exchange_length h); Intro Hel; Clear h; WhyBounds
  | [ |- (Zle `0` ?) /\ (Zlt ? (array_length ?1)) ] -> 
    Try (CallSubst ?1; Simpl; Omega)
  | _ -> 
    Idtac.

Tactic Definition WhyStoreOther :=
  Rewrite store_def_2; WhyArrays; WhyBounds.

Tactic Definition WhyLength t :=
  Subst t; Simpl; Try Omega.

