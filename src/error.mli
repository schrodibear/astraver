
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: error.mli,v 1.1 2001-08-15 21:08:51 filliatr Exp $ *)

open Ident
open Types
open Ast
open Format

type error = 
  | UnboundVariable of Ident.t
  | UnboundReference of Ident.t
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
  | PartialApp
  | NotExpectedType of (formatter -> unit)
  | ExpectsAType of Ident.t
  | ExpectsATerm of Ident.t
  | ShouldBeVariable
  | ShouldBeReference
  | NoVariableAtDate of Ident.t * string

exception Error of (Location.t option) * error

val report : formatter -> error -> unit

val unbound_variable : Ident.t -> Location.t option -> 'a
val unbound_reference : Ident.t -> Location.t option -> 'a

val clash : Ident.t -> Location.t option -> 'a
val not_defined : Ident.t -> 'a

val check_for_reference : Location.t -> Ident.t -> type_v -> unit
val check_for_array     : Location.t -> Ident.t -> type_v -> unit

val check_for_index_type : Location.t -> type_v -> unit
val check_no_effect : Location.t -> Effect.t -> unit
val should_be_boolean : Location.t -> 'a
val test_should_be_annotated : Location.t -> 'a
val if_branches : Location.t -> 'a

val check_for_not_mutable : Location.t -> type_v -> unit
val check_for_pure_type : Location.t -> type_v -> unit
val check_for_let_ref : Location.t -> type_v -> unit

val variant_informative : Location.t -> 'a
val should_be_informative : Location.t -> 'a

val app_of_non_function : Location.t -> 'a
val partial_app : Location.t -> 'a
val expected_type : Location.t -> (formatter -> unit) -> 'a
val expects_a_type : Ident.t -> Location.t -> 'a
val expects_a_term : Ident.t -> 'a
val should_be_a_variable : Location.t -> 'a
val should_be_a_reference : Location.t -> 'a

val no_variable_at_date : Ident.t -> string -> 'a
