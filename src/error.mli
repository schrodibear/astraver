
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: error.mli,v 1.2 2001-08-17 00:52:38 filliatr Exp $ *)

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

exception Error of (Loc.t option) * error

val report : formatter -> error -> unit

val unbound_variable : Ident.t -> Loc.t option -> 'a
val unbound_reference : Ident.t -> Loc.t option -> 'a

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
val partial_app : Loc.t -> 'a
val expected_type : Loc.t -> (formatter -> unit) -> 'a
val expects_a_type : Ident.t -> Loc.t -> 'a
val expects_a_term : Ident.t -> 'a
val should_be_a_variable : Loc.t -> 'a
val should_be_a_reference : Loc.t -> 'a

val no_variable_at_date : Ident.t -> string -> 'a

val check_for_non_constant : Loc.t -> Logic.term -> unit
