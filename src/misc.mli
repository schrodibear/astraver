(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: misc.mli,v 1.10 2002-02-28 16:15:13 filliatr Exp $ i*)

(* Some misc. functions *)

open Logic
open Types

val is_mutable : type_v -> bool
val is_pure : type_v -> bool

val named_app : (predicate -> predicate) -> assertion -> assertion
val pre_app : (predicate -> predicate) -> precondition -> precondition
val post_app : (predicate -> predicate) -> postcondition -> postcondition

val anonymous : predicate -> assertion
val anonymous_pre : bool -> predicate -> precondition
val out_post : postcondition option -> predicate
val pre_of_assert : bool -> assertion -> precondition
val assert_of_pre : precondition -> assertion

val force_post_name : postcondition option -> postcondition option
val force_bool_name : postcondition option -> postcondition option

val map_succeed : ('a -> 'b) -> 'a list -> 'b list

val option_app : ('a -> 'b) -> 'a option -> 'b option

val list_of_some : 'a option -> 'a list
val difference : 'a list -> 'a list -> 'a list

val list_combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list

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
val papplist : predicate -> term list -> predicate

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

(*s Smart constructors. *)

val ttrue : term
val tfalse : term
val tresult : term

val relation : Ident.t -> term -> term -> predicate
val not_relation : Ident.t -> term -> term -> predicate

val lt : term -> term -> predicate
val le : term -> term -> predicate
val gt : term -> term -> predicate
val ge : term -> term -> predicate
val eq : term -> term -> predicate
val neq : term -> term -> predicate

val pif : term -> predicate -> predicate -> predicate
val pand : predicate -> predicate -> predicate
val por : predicate -> predicate -> predicate
val pnot : predicate -> predicate

(*s Pretty-print *)

open Format

val print_list : formatter -> (formatter -> unit -> unit) -> 
  (formatter -> 'a -> unit) -> 'a list -> unit
val comma : formatter -> unit -> unit
val nothing : formatter -> unit -> unit
val hov : int -> formatter -> ('a -> unit) -> 'a -> unit

val print_term : formatter -> term -> unit
val print_predicate : formatter -> predicate -> unit

val warning : string -> unit
