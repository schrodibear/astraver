(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: error.mli,v 1.6 2002-03-11 15:17:57 filliatr Exp $ i*)

(*s Errors. *)

open Ident
open Types
open Ast
open Format

type error = 
  | UnboundVariable of Ident.t
  | UnboundReference of Ident.t
  | UnboundLabel of string
  | Clash of Ident.t
  | Undefined of Ident.t
  | NotAReference of Ident.t
  | NotAnArray of Ident.t
  | NotAnIndex
  | HasSideEffects
  | ShouldBeBoolean
  | ShouldBeAnnotated
  | CannotBeMutable
  | MustBePure
  | BranchesSameType
  | LetRef
  | VariantInformative
  | ShouldBeInformative
  | AppNonFunction
  | TooManyArguments
  | TooComplexArgument
  | PartialApp
  | TermExpectedType of (formatter -> unit) * (formatter -> unit)
  | ExpectedType of (formatter -> unit)
  | ExpectsAType of Ident.t
  | ExpectsATerm of Ident.t
  | ShouldBeVariable of Ident.t
  | ShouldBeReference of Ident.t
  | ShouldNotBeReference
  | IllTypedArgument of (formatter -> unit)
  | NoVariableAtDate of Ident.t * string

exception Error of (Loc.t option) * error

val report : formatter -> error -> unit

val unbound_variable : Ident.t -> Loc.t option -> 'a
val unbound_reference : Ident.t -> Loc.t option -> 'a
val unbound_label : string -> Loc.t option -> 'a

val clash : Ident.t -> Loc.t option -> 'a
val not_defined : Ident.t -> 'a

val check_for_reference : Loc.t -> Ident.t -> type_v -> unit
val check_for_array     : Loc.t -> Ident.t -> type_v -> unit

val check_for_index_type : Loc.t -> type_v -> unit
val check_no_effect : Loc.t -> Effect.t -> unit
val should_be_boolean : Loc.t -> 'a
val test_should_be_annotated : Loc.t -> 'a
val if_branches : Loc.t -> 'a

val check_for_not_mutable : Loc.t -> type_v -> unit
val check_for_pure_type : Loc.t -> type_v -> unit
val check_for_let_ref : Loc.t -> type_v -> unit

val variant_informative : Loc.t -> 'a
val should_be_informative : Loc.t -> 'a

val app_of_non_function : Loc.t -> 'a
val too_many_arguments : Loc.t -> 'a
val too_complex_argument : Loc.t -> 'a
val partial_app : Loc.t -> 'a
val term_expected_type : 
  Loc.t -> (formatter -> unit) -> (formatter -> unit) -> 'a
val expected_type : Loc.t -> (formatter -> unit) -> 'a
val expects_a_type : Ident.t -> Loc.t -> 'a
val expects_a_term : Ident.t -> 'a
val should_be_a_variable : Loc.t -> Ident.t -> 'a
val should_be_a_reference : Loc.t -> Ident.t -> 'a
val should_not_be_a_reference : Loc.t -> 'a
val ill_typed_argument : Loc.t -> (formatter -> unit) -> 'a

val no_variable_at_date : Ident.t -> string -> 'a

val check_for_non_constant : Loc.t -> Logic.term -> unit
