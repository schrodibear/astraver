(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



(*s Errors. *)

open Format

type t = 
  | UnboundVariable of Ident.t
  | UnboundReference of Ident.t
  | UnboundArray of Ident.t
  | UnboundLabel of string
  | ReboundLabel of string
  | UnboundException of Ident.t
  | UnboundType of Ident.t
  | Clash of Ident.t
  | ClashParam of Ident.t
  | ClashExn of Ident.t
  | ClashRef of Ident.t
  | ClashType of Ident.t
  | Undefined of Ident.t
  | NotAReference of Ident.t
  | NotAnArray of Ident.t
  | NotAnIndex
  | HasSideEffects
  | ShouldBeBoolean
  | ShouldBeAlgebraic
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
  | ExpectedType2 of (formatter -> unit) * (formatter -> unit)
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
  | MutableMutable
  | PolymorphicGoal
  | NonExhaustive of Ident.t
  | PatternBadArity
  | TypeBadArity
  | TypeArity of Ident.t * int * int
  | GlobalWithEffects of Ident.t * Effect.t
  | IllformedPattern
  | CannotGeneralize
  | IllegalComparison of (formatter -> unit)

