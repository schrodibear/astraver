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

(*i $Id: report.ml,v 1.9 2005-06-21 07:45:04 filliatr Exp $ i*)

open Ident
open Logic
open Types
open Ast
open Format
open Error

exception Error of (Loc.t option) * Error.t

let report fmt = function
  | AnyMessage s ->
      fprintf fmt "Error: %s" s
  | UnboundVariable id ->
      fprintf fmt "Unbound variable %s" (Ident.string id)
  | UnboundReference id ->
      fprintf fmt "Unbound reference %s" (Ident.string id)
  | UnboundArray id ->
      fprintf fmt "Unbound array %s" (Ident.string id)
  | UnboundLabel s ->
      fprintf fmt "Unbound label '%s'" s
  | UnboundException id ->
      fprintf fmt "Unbound exception '%s'" (Ident.string id)
  | Clash id ->
      fprintf fmt "Clash with previous constant %s" (Ident.string id)
  | ClashExn id ->
      fprintf fmt "Clash with previous exception %s" (Ident.string id)
  | ClashRef id ->
      fprintf fmt "Clash with previous reference or array %s" (Ident.string id)
  | Undefined id ->
      fprintf fmt "The object %s is undefined" (Ident.string id)
  | NotAReference id ->
      fprintf fmt "%s is not a reference" (Ident.string id)
  | NotAnArray id ->
      fprintf fmt "%s is not an array" (Ident.string id)
  | NotAnIndex ->
      fprintf fmt "@[This expression is an index@ and should have type int@]"
  | HasSideEffects ->
      fprintf fmt "This expression should not have side effects"
  | ShouldBeBoolean ->
      fprintf fmt "This expression should have type bool"
  | ShouldBeAnnotated ->
      fprintf fmt "This test should be annotated"
  | CannotBeMutable ->
      fprintf fmt "This expression cannot be a mutable"
  | MustBePure ->
      fprintf fmt "@[This expression must be pure@ ";
      fprintf fmt "(i.e. neither a mutable nor a function)@]"
  | BranchesSameType ->
      fprintf fmt "@[The two branches of an `if' expression@ ";
      fprintf fmt "should have the same type@]"
  | LetRef ->
      fprintf fmt "References can only be bound in pure terms"
  | VariantInformative ->
      fprintf fmt "A variant should be informative"
  | ShouldBeInformative ->
      fprintf fmt "This term should be informative"
  | AppNonFunction ->
      fprintf fmt "@[This term cannot be applied@ ";
      fprintf fmt "(either it is not a function@ ";
      fprintf fmt "or it is applied to non pure arguments)@]"
  | TooManyArguments ->
      fprintf fmt "@[Too many arguments@]"
  | TooComplexArgument ->
      fprintf fmt 
	"@[This argument is too complex; application cannot be given a type@]"
  | Alias id ->
      fprintf fmt "@[Application to %a creates an alias@]" Ident.print id
  | PartialApp ->
      fprintf fmt "@[This function does not have@ ";
      fprintf fmt "the right number of arguments@]"
  | ExpectedType v ->
      fprintf fmt "@[This term is expected to have type@ ";
      v fmt; fprintf fmt "@]"
  | TermExpectedType (t,v) ->
      fprintf fmt "@[Term "; t fmt; fprintf fmt "@ is expected to have type@ ";
      v fmt; fprintf fmt "@]"
  | ExpectsAType id ->
      fprintf fmt "@[The argument %s@ " (Ident.string id);
      fprintf fmt "in this application is supposed to be a type@]"
  | ExpectsATerm id ->
      fprintf fmt "@[The argument %s@ " (Ident.string id);
      fprintf fmt "in this application is supposed to be a term@]"
  | ShouldBeVariable ->
      fprintf fmt "@[This argument should be a variable@]"
  | ShouldBeReference id ->
      fprintf fmt "@[The argument %a@ " Ident.print id;
      fprintf fmt "in this application should be a reference@]"
  | ShouldNotBeReference ->
      fprintf fmt "@[This argument should not be a reference@]"
  | IllTypedArgument f ->
      fprintf fmt "@[This argument should have type@ "; f fmt; fprintf fmt "@]"
  | NoVariableAtDate (id, d) ->
      fprintf fmt "Variable %a is unknown at date %s" Ident.print id d
  | MutableExternal ->
      fprintf fmt "@[An external value cannot be mutable;@ ";
      fprintf fmt "use parameter instead@]"
  | ExceptionArgument (id, true) ->
      fprintf fmt "Exception %a needs an argument" Ident.print id
  | ExceptionArgument (id, false) ->
      fprintf fmt "Exception %a has no argument" Ident.print id
  | CannotBeRaised id ->
      fprintf fmt "Exception %a cannot be raised by this expression" 
	Ident.print id
  | MutableMutable ->
      fprintf fmt 
	"A mutable type cannot contain another mutable type or a function"
  | PolymorphicGoal ->
      fprintf fmt "A goal cannot be polymorphic"

let is_mutable = function Ref _ | Array _ -> true | _ -> false
let is_pure = function PureType _ -> true | _ -> false

let raise_located loc e = raise (Error (Some loc, e))
let raise_unlocated e = raise (Error (None, e))
let raise_locop locop e = raise (Error (locop, e))


let rec explain_exception fmt = function
  | Parsing.Parse_error -> 
      fprintf fmt "Syntax error"
  | Stream.Error s -> 
      fprintf fmt "Syntax error: %s" s
  | Error (Some loc, e) | Stdpp.Exc_located (_, Error (Some loc, e)) ->
      fprintf fmt "%a%a" Loc.report loc report e
  | Stdpp.Exc_located (loc, e) ->
      fprintf fmt "%a%a" Loc.report (Compat.make_loc loc) explain_exception e
  | Error (_, e) ->
      report fmt e
  | e ->
      fprintf fmt "Anomaly: %s" (Printexc.to_string e); raise e

