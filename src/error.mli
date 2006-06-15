(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: error.mli,v 1.24 2006-06-15 09:58:30 lescuyer Exp $ i*)

(*s Errors. *)

open Format

type t = 
  | UnboundVariable of Ident.t
  | UnboundReference of Ident.t
  | UnboundArray of Ident.t
  | UnboundLabel of string
  | UnboundException of Ident.t
  | UnboundType of Ident.t
  | Clash of Ident.t
  | ClashExn of Ident.t
  | ClashRef of Ident.t
  | ClashType of Ident.t
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
  | TypeBadArity
  | TypeArity of Ident.t * int * int
  | GlobalWithEffects of Ident.t * Effect.t
  | IllformedPattern
  | CannotGeneralize
