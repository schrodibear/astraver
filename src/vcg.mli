
(*s Verification Conditions Generator. *)

type sequent_element =
  | Svar of Ident.t * type_v
  | Spred of predicate

type sequent = sequent_element list

val vcg : cc_term -> sequent list

