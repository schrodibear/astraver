(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: misc.mli,v 1.20 2002-03-14 16:13:41 filliatr Exp $ i*)

(* Some misc. functions *)

open Logic
open Types
open Ast

val is_mutable : type_v -> bool
val is_pure : type_v -> bool

val named_app : (predicate -> predicate) -> assertion -> assertion
val pre_app : (predicate -> predicate) -> precondition -> precondition
val post_app : (predicate -> predicate) -> postcondition -> postcondition
val optpost_app : 
  (predicate -> predicate) -> postcondition option -> postcondition option

val anonymous : predicate -> assertion
val anonymous_pre : bool -> predicate -> precondition
val out_post : postcondition option -> predicate
val pre_of_assert : bool -> assertion -> precondition
val assert_of_pre : precondition -> assertion

val force_post_name : postcondition option -> postcondition option
val force_bool_name : postcondition option -> postcondition option

val map_succeed : ('a -> 'b) -> 'a list -> 'b list

val option_app : ('a -> 'b) -> 'a option -> 'b option
val option_iter : ('a -> unit) -> 'a option -> unit

val list_of_some : 'a option -> 'a list
val difference : 'a list -> 'a list -> 'a list

val list_combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list

val if_labelled : (Ident.t * string -> unit) -> Ident.t -> unit

type avoid = Ident.set
val renaming_of_ids : avoid -> Ident.t list -> (Ident.t * Ident.t) list * avoid

val reset_names : unit -> unit
val pre_name    : Ident.name -> Ident.t
val post_name   : Ident.name -> Ident.t
val inv_name    : Ident.name -> Ident.t
val test_name   : Ident.name -> Ident.t
val bool_name   : unit -> Ident.t
val variant_name : Ident.name -> Ident.t
val phi_name    : unit -> Ident.t
val for_name    : unit -> Ident.t
val label_name  : unit -> string
val fresh_var : unit -> Ident.t

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

val mlize_type : type_v -> pure_type

(*s Smart constructors for terms and predicates. *)

val ttrue : term
val tfalse : term
val tresult : term
val tvoid : term

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

(*s functions over CC terms *)

val cc_applist : cc_term -> cc_term list -> cc_term

(*s functions over AST *)

val arg_loc : parsed_info arg -> Loc.t

(*s Pretty-print *)

open Format

val print_list : 
  (formatter -> unit -> unit) -> 
  (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
val comma : formatter -> unit -> unit
val arrow : formatter -> unit -> unit
val nothing : formatter -> unit -> unit
val hov : int -> formatter -> ('a -> unit) -> 'a -> unit

val print_term : formatter -> term -> unit
val print_predicate : formatter -> predicate -> unit
val print_assertion : formatter -> assertion -> unit
val print_wp : formatter -> assertion option -> unit

val warning : string -> unit
