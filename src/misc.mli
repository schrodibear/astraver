
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: misc.mli,v 1.1 2001-08-15 21:08:52 filliatr Exp $ *)

(* Some misc. functions *)

open Logic

val reraise_with_loc : Location.t -> ('a -> 'b) -> 'a -> 'b

val list_of_some : 'a option -> 'a list
val difference : 'a list -> 'a list -> 'a list

val at_id : Ident.t -> string -> Ident.t
val un_at : Ident.t -> Ident.t * string
val is_at : Ident.t -> bool

val adr_id : Ident.t -> Ident.t

type avoid = Ident.set
val renaming_of_ids : avoid -> Ident.t list -> (Ident.t * Ident.t) list * avoid

val reset_names : unit -> unit
val pre_name    : Ident.name -> Ident.t
val post_name   : Ident.name -> Ident.t
val inv_name    : Ident.name -> Ident.t
val test_name   : Ident.name -> Ident.t
val bool_name   : unit -> Ident.t
val var_name    : Ident.name -> Ident.t
val phi_name    : unit -> Ident.t
val for_name    : unit -> Ident.t
val label_name  : unit -> string

val id_of_name : Ident.name -> Ident.t

(*s Functions over terms and predicates. *)

val term_vars : term -> Ident.set
val predicate_vars : predicate -> Ident.set

val subst_in_predicate : (Ident.t * Ident.t) list -> predicate -> predicate

(* CIC terms *)

(*i
val isevar : constr

val subst_in_constr : (Ident.t * Ident.t) list -> constr -> constr
val subst_in_ast : (Ident.t * Ident.t) list -> Coqast.t -> Coqast.t
val subst_ast_in_ast : (Ident.t * Coqast.t) list -> Coqast.t -> Coqast.t
val real_subst_in_constr : (Ident.t * constr) list -> constr -> constr

val constant : string -> constr
val coq_constant : string list -> string -> section_path
val conj : constr -> constr -> constr

val coq_true : constr
val coq_false : constr

val connective_and : Ident.t
val connective_or  : Ident.t
val connective_not : Ident.t
val is_connective : Ident.t -> bool

val n_mkNamedProd : constr -> (Ident.t * constr) list -> constr
val n_lambda  : constr -> (Ident.t * constr) list -> constr
val abstract : (Ident.t * constr) list -> constr -> constr
i*)

(*s Pretty-print *)

open Format

val print_list : formatter -> (formatter -> unit -> unit) -> 
  (formatter -> 'a -> unit) -> 'a list -> unit

val print_term : formatter -> term -> unit
val print_predicate : formatter -> predicate -> unit

(*s For debugging purposes... *)

val warning : string -> unit
val debug : bool ref
