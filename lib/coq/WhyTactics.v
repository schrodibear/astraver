
Require WhyArrays.
Require WhyPermut.

Tactic Definition CallSubst x := Subst x.

Tactic Definition ArrayLength :=
  Match Context With
  | [ h: (exchange ? ? ? ?) |- ? ] ->
    (Rewrite (exchange_length h); Try Omega) Orelse 
    (Rewrite <- (exchange_length h); Try Omega)
  | [ h: (sub_permut ? ? ? ?) |- ? ] ->
    (Rewrite (sub_permut_length h); Try Omega) Orelse 
    (Rewrite <- (sub_permut_length h); Try Omega)
  | [ h: (permut ? ? ? ?) |- ? ] ->
    (Rewrite (permut_length h); Try Omega) Orelse 
    (Rewrite <- (permut_length h); Try Omega)
  | _ -> 
    Idtac.


