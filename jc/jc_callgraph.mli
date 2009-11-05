
val compute_logic_calls : 
  Jc_fenv.logic_info -> Jc_fenv.term_or_assertion -> unit
(** (compute_logic_calls f t) adds to the set of known calls of logic function 
    f the logic calls that occur in t
*)

val compute_calls : 
  Jc_fenv.fun_info -> Jc_fenv.fun_spec -> Jc_constructors.expr -> unit
(** (compute_calls f spec body) adds to the set of known calls of
     program f the logic calls that occur in spec and the program
     calls that occur in body
*)

val compute_logic_components :   
  (int, (Jc_fenv.logic_info * Jc_fenv.term_or_assertion)) Jc_stdlib.Hashtbl.t 
  -> Jc_fenv.logic_info list array

val compute_components :   
  (int, (Jc_fenv.fun_info * Loc.position * Jc_fenv.fun_spec * Jc_fenv.expr option)) Jc_stdlib.Hashtbl.t 
  -> Jc_fenv.fun_info list array
