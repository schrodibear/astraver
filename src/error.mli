(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: error.mli,v 1.17 2002-10-15 11:49:11 filliatr Exp $ i*)

(*s Errors. *)

open Format

type t = 
  | UnboundVariable of Ident.t
  | UnboundReference of Ident.t
  | UnboundArray of Ident.t
  | UnboundLabel of string
  | UnboundException of Ident.t
  | Clash of Ident.t
  | ClashExn of Ident.t
  | ClashRef of Ident.t
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
  | Alias of Ident.t
  | PartialApp
  | TermExpectedType of (formatter -> unit) * (formatter -> unit)
  | ExpectedType of (formatter -> unit)
  | ExpectsAType of Ident.t
  | ExpectsATerm of Ident.t
  | ShouldBeVariable
  | ShouldBeReference of Ident.t
  | ShouldNotBeReference
  | IllTypedArgument of (formatter -> unit)
  | NoVariableAtDate of Ident.t * string
  | MutableExternal
  | AnyMessage of string
  | ExceptionArgument of Ident.t * bool
  | CannotBeRaised of Ident.t
