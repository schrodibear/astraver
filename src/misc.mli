
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: misc.mli,v 1.4 2001-08-21 20:57:02 filliatr Exp $ *)

(* Some misc. functions *)

open Logic

val map_succeed : ('a -> 'b) -> 'a list -> 'b list

val reraise_with_loc : Loc.t -> ('a -> 'b) -> 'a -> 'b

val option_app : ('a -> 'b) -> 'a option -> 'b option

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

val applist : term -> term list -> term

val term_vars : term -> Ident.set
val predicate_vars : predicate -> Ident.set

val subst_in_term : (Ident.t * Ident.t) list -> term -> term
val tsubst_in_term : (Ident.t * term) list -> term -> term

val subst_in_predicate : (Ident.t * Ident.t) list -> predicate -> predicate
val tsubst_in_predicate : (Ident.t * term) list -> predicate -> predicate
val bsubst_in_predicate : (Ident.bound * term) list -> predicate -> predicate

val equals_true : term -> term
val equals_false : term -> term

val mlize_type : Types.type_v -> pure_type

val occur_term : Ident.t -> term -> bool
val occur_predicate : Ident.t -> predicate -> bool

val ttrue : term
val tfalse : term
val ptrue : predicate
val pfalse : predicate
val pif : predicate -> predicate -> predicate -> predicate
val pand : predicate -> predicate -> predicate
val por : predicate -> predicate -> predicate
val pnot : predicate -> predicate


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
val comma : formatter -> unit -> unit
val nothing : formatter -> unit -> unit
val hov : int -> formatter -> ('a -> unit) -> 'a -> unit

val print_term : formatter -> term -> unit
val print_predicate : formatter -> predicate -> unit

(*s For debugging purposes... *)

val warning : string -> unit
val debug : bool ref
