(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: misc.mli,v 1.38 2002-09-12 13:20:55 filliatr Exp $ i*)

(* Some misc. functions *)

open Logic
open Types
open Ast
open Ptree
open Cc

val is_mutable : type_v -> bool
val is_pure : type_v -> bool

val named_app : (predicate -> predicate) -> assertion -> assertion
val pre_app : (predicate -> predicate) -> precondition -> precondition
val post_app : (predicate -> predicate) -> postcondition -> postcondition
val optpost_app : 
  (predicate -> predicate) -> postcondition option -> postcondition option

val anonymous : 'a -> 'a asst
val anonymous_pre : bool -> predicate -> precondition
val pre_of_assert : bool -> 'a asst -> 'a pre
val assert_of_pre : precondition -> assertion

val force_post_name : postcondition option -> postcondition option
val force_bool_name : postcondition option -> postcondition option

val map_succeed : ('a -> 'b) -> 'a list -> 'b list

val option_app : ('a -> 'b) -> 'a option -> 'b option
val option_iter : ('a -> unit) -> 'a option -> unit

val list_of_some : 'a option -> 'a list
val difference : 'a list -> 'a list -> 'a list

val list_combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list

val list_first : ('a -> 'b) -> 'a list -> 'b

val if_labelled : (Ident.t * string -> unit) -> Ident.t -> unit

type avoid = Ident.set
val renaming_of_ids : avoid -> Ident.t list -> (Ident.t * Ident.t) list * avoid

val pre_name    : Ident.name -> Ident.t
val post_name   : Ident.name -> Ident.t
val inv_name    : Ident.name -> Ident.t
val test_name   : Ident.name -> Ident.t

val bool_name   : unit -> Ident.t
val variant_name : unit -> Ident.t
val phi_name    : unit -> Ident.t
val for_name    : unit -> Ident.t
val label_name  : unit -> string
val wf_name     : unit -> Ident.t
val fresh_var   : unit -> Ident.t

val post_name_from : Ident.name -> Ident.t

val reset_names : unit -> unit

val id_of_name : Ident.name -> Ident.t

val rationalize : string -> string * string

(*s Functions over terms and predicates. *)

val applist : term -> term list -> term
val papplist : predicate -> term list -> predicate

val predicate_of_term : term -> predicate

val term_vars : term -> Ident.set
val predicate_vars : predicate -> Ident.set
val post_vars : postcondition -> Ident.set

val subst_in_term : var_substitution -> term -> term
val tsubst_in_term : substitution -> term -> term

val subst_in_predicate : var_substitution -> predicate -> predicate
val tsubst_in_predicate : substitution -> predicate -> predicate

val subst_one : Ident.t -> term -> substitution
val subst_onev : Ident.t -> Ident.t -> var_substitution

val type_v_subst : var_substitution -> type_v -> type_v
val type_c_subst : var_substitution -> type_c -> type_c

val type_v_rsubst : substitution -> type_v -> type_v
val type_c_rsubst : substitution -> type_c -> type_c

val ptype_c_of_v : ptype_v -> ptype_c
val type_c_of_v : type_v -> type_c
val make_arrow : type_v binder list -> type_c -> type_v

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
val make_int_relation : Ident.t -> Ident.t

val lt : term -> term -> predicate
val le : term -> term -> predicate
val lt_int : term -> term -> predicate
val le_int : term -> term -> predicate
val gt : term -> term -> predicate
val ge : term -> term -> predicate
val ge_float : term -> term -> predicate
val eq : term -> term -> predicate
val neq : term -> term -> predicate

val pif : term -> predicate -> predicate -> predicate
val pand : predicate -> predicate -> predicate
val por : predicate -> predicate -> predicate
val pnot : predicate -> predicate

val simplify : predicate -> predicate

(*s functions over CC terms *)

val cc_applist : 'a cc_term -> 'a cc_term list -> 'a cc_term
val cc_lam : cc_binder list -> 'a cc_term -> 'a cc_term

val tt_arrow : cc_binder list -> cc_type -> cc_type

(*s functions over AST *)

val arg_loc : Ptree.arg -> Loc.t

(*s Pretty-print *)

open Format

val print_list : 
  (formatter -> unit -> unit) -> 
  (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
val space : formatter -> unit -> unit
val comma : formatter -> unit -> unit
val semi : formatter -> unit -> unit
val arrow : formatter -> unit -> unit
val nothing : formatter -> unit -> unit
val hov : int -> formatter -> ('a -> unit) -> 'a -> unit

val print_term : formatter -> term -> unit
val print_predicate : formatter -> predicate -> unit
val print_assertion : formatter -> assertion -> unit
val print_wp : formatter -> postcondition option -> unit

val warning : string -> unit
