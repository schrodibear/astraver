
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: error.ml,v 1.3 2001-08-23 20:24:34 filliatr Exp $ *)

open Ident
open Logic
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
  | NotExpectedType of (formatter -> unit) * (formatter -> unit)
  | ExpectsAType of Ident.t
  | ExpectsATerm of Ident.t
  | ShouldBeVariable of Ident.t
  | ShouldBeReference of Ident.t
  | IllTypedArgument of (formatter -> unit)
  | NoVariableAtDate of Ident.t * string

exception Error of (Loc.t option) * error

let report fmt = function
  | UnboundVariable id ->
      fprintf fmt "Unbound variable %s" (Ident.string id)
  | UnboundReference id ->
      fprintf fmt "Unbound reference or array %s" (Ident.string id)
  | Clash id ->
      fprintf fmt "Clash with previous constant %s" (Ident.string id)
  | Undefined id ->
      fprintf fmt "The object %s is undefined" (Ident.string id)
  | NotAReference id ->
      fprintf fmt "%s is not a refenrece" (Ident.string id)
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
  | PartialApp ->
      fprintf fmt "@[This function does not have@ ";
      fprintf fmt "the right number of arguments@]"
  | NotExpectedType (t,v) ->
      fprintf fmt "@[Term "; t fmt; fprintf fmt "@ is expected to have type@ ";
      v fmt; fprintf fmt "@]"
  | ExpectsAType id ->
      fprintf fmt "@[The argument %s@ " (Ident.string id);
      fprintf fmt "in this application is supposed to be a type@]"
  | ExpectsATerm id ->
      fprintf fmt "@[The argument %s@ " (Ident.string id);
      fprintf fmt "in this application is supposed to be a term@]"
  | ShouldBeVariable id ->
      fprintf fmt "@[The argument %s@ " (Ident.string id);
      fprintf fmt "in this application should be a variable@]"
  | ShouldBeReference id ->
      fprintf fmt "@[The argument %s@ " (Ident.string id);
      fprintf fmt "in this application should be a reference@]"
  | IllTypedArgument f ->
      fprintf fmt "@[This argument should have type@ "; f fmt; fprintf fmt "@]"
  | NoVariableAtDate (id, d) ->
      fprintf fmt "Variable %s is unknown at date %s" (Ident.string id) d

let is_mutable = function Ref _ | Array _ -> true | _ -> false
let is_pure = function PureType _ -> true | _ -> false

let raise_with_loc loc e = raise (Error (loc, e))

let unbound_variable id loc = raise_with_loc loc (UnboundVariable id)

let unbound_reference id loc = raise_with_loc loc (UnboundReference id)

let clash id loc = raise_with_loc loc (Clash id)

let not_defined id = raise_with_loc None (Undefined id)

let check_for_reference loc id = function
  | Ref _ -> ()
  | _ -> raise_with_loc (Some loc) (NotAReference id)

let check_for_array loc id = function
  | Array _ -> ()
  | _ -> raise_with_loc (Some loc) (NotAnArray id)

let is_int_type = function
  | PureType PTint -> true
  | _ -> false 

let check_for_index_type loc v =
  let is_index = is_int_type v in
  if not is_index then raise_with_loc (Some loc) NotAnIndex

let check_no_effect loc ef =
  if not (Effect.get_writes ef = []) then 
    raise_with_loc (Some loc) HasSideEffects

let should_be_boolean loc = raise_with_loc (Some loc) ShouldBeBoolean

let test_should_be_annotated loc = raise_with_loc (Some loc) ShouldBeAnnotated

let if_branches loc = raise_with_loc (Some loc) BranchesSameType

let check_for_not_mutable loc v = 
  if is_mutable v then raise_with_loc (Some loc) CannotBeMutable

let check_for_pure_type loc v =
  if not (is_pure v) then raise_with_loc (Some loc) MustBePure

let check_for_let_ref loc v =
  if not (is_pure v) then raise_with_loc (Some loc) LetRef

let variant_informative loc = raise_with_loc (Some loc) VariantInformative
let should_be_informative loc = raise_with_loc (Some loc) ShouldBeInformative

let app_of_non_function loc = raise_with_loc (Some loc) AppNonFunction
  
let partial_app loc = raise_with_loc (Some loc) PartialApp
  
let expected_type loc t v = raise_with_loc (Some loc) (NotExpectedType (t,v))

let expects_a_type id loc = raise_with_loc (Some loc) (ExpectsAType id)

let expects_a_term id = raise_with_loc None (ExpectsATerm id)

let should_be_a_variable loc id = 
  raise_with_loc (Some loc) (ShouldBeVariable id)
   
let should_be_a_reference loc id = 
  raise_with_loc (Some loc) (ShouldBeReference id)

let ill_typed_argument loc t = raise_with_loc (Some loc) (IllTypedArgument t)

let no_variable_at_date id d = raise_with_loc None (NoVariableAtDate (id,d))

let check_for_non_constant loc = function
  | Tconst _ -> raise_with_loc (Some loc) AppNonFunction
  | _ -> ()

