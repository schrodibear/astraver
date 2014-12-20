(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
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
  | UnboundVariable of Why_ident.t
  | UnboundReference of Why_ident.t
  | UnboundArray of Why_ident.t
  | UnboundLabel of string
  | ReboundLabel of string
  | UnboundException of Why_ident.t
  | UnboundType of Why_ident.t
  | Clash of Why_ident.t
  | ClashParam of Why_ident.t
  | ClashExn of Why_ident.t
  | ClashRef of Why_ident.t
  | ClashType of Why_ident.t
  | Undefined of Why_ident.t
  | NotAReference of Why_ident.t
  | NotAnArray of Why_ident.t
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
  | Alias of Why_ident.t
  | PartialApp
  | TermExpectedType of (formatter -> unit) * (formatter -> unit)
  | ExpectedType of (formatter -> unit)
  | ExpectedType2 of (formatter -> unit) * (formatter -> unit)
  | ExpectsAType of Why_ident.t
  | ExpectsATerm of Why_ident.t
  | ShouldBeVariable
  | ShouldBeReference of Why_ident.t
  | ShouldNotBeReference
  | IllTypedArgument of (formatter -> unit)
  | NoVariableAtDate of Why_ident.t * string
  | MutableExternal
  | AnyMessage of string
  | ExceptionArgument of Why_ident.t * bool
  | CannotBeRaised of Why_ident.t
  | MutableMutable
  | PolymorphicGoal
  | NonExhaustive of Why_ident.t
  | PatternBadArity
  | TypeBadArity
  | TypeArity of Why_ident.t * int * int
  | GlobalWithEffects of Why_ident.t * Why_effect.t
  | IllformedPattern
  | CannotGeneralize
  | IllegalComparison of (formatter -> unit)
