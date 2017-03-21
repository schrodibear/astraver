(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2015                                               *)
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
(*  Jessie2 fork:                                                         *)
(*    Mikhail MANDRYKIN, ISP RAS       (adaptation for Linux sources)     *)
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

open Lexing
open Format

type vc_kind =
  | JCVCvar_decr
  | JCVCarith_overflow
  | JCVCpointer_deref
  | JCVCpointer_deref_bounds
  | JCVCpointer_shift
  | JCVCseparation
  | JCVCindex_bounds
  | JCVCuser_call of string
  | JCVCdiv_by_zero
  | JCVCalloc_size
  | JCVCenum_cast
  | JCVCfp_overflow
  | JCVCpre of string
  | JCVCassigns
  | JCVCallocates
  | JCVCensures
  | JCVCassertion of Position.t
  | JCVCcheck of string
  | JCVCpost
  | JCVCglobal_invariant of string
  | JCVCrequires

type why_label = {
  l_kind     : vc_kind option;
  l_behavior : string;
  l_pos      : Position.t
}

type single = Single
type double = Double

type 'prec precision =
  | Single : single precision
  | Double : double precision

type arbitrary_precision = Arbitrary_precision

type 'prec real =
  | Float : 'prec precision -> 'prec precision real
  | Real : arbitrary_precision real

type _8 = S8
type _16 = S16
type _32 = S32
type _64 = S64

type _ bit =
  | X8 : _8 bit
  | X16 : _16 bit
  | X32 : _32 bit
  | X64 : _64 bit

type signed = Signed
type unsigned = Unsigned

type _ repr =
  | Signed : signed repr
  | Unsigned : unsigned repr

type ('repr, 'bit) xintx = Xintx of 'repr repr * 'bit bit

type _ enum = ..

module type Enum =
sig
  type t
  type 'a enum += E : t enum
  val name : string
end

type _ bounded =
  | Int : ('repr, 'bit) xintx -> ('repr, 'bit) xintx bounded
  | Enum : (module Enum with type t = 'a) -> 'a enum bounded

type unbounded = Unbounded

type 'bounded integer =
  | Int : 'a repr * 'b bit -> ('a repr, 'b bit) xintx bounded integer
  | Enum : (module Enum with type t = 'a) -> 'a enum bounded integer
  | Integer : unbounded integer

type 'a number =
  | Integral : 'bounded integer -> 'bounded integer number
  | Real : 'prec real -> 'prec real number

type void = Void

type boolean = Boolean

type ('params, 'result) func =
  | B_int_op :
      [ `Add | `Sub | `Mul | `Div | `Mod | `Min | `Max ] ->
    (unbounded integer number * (unbounded integer number * unit), unbounded integer number) func
  | U_int_op : [ `Neg | `Abs ] -> (unbounded integer number * unit, unbounded integer number) func
  | B_bint_op :
      [ `Add | `Sub | `Mul | `Div | `Mod ] * 'a bounded integer * [ `Check | `Modulo ] ->
    ('a bounded integer number * ('a bounded integer number * unit), 'a bounded integer number) func
  | U_bint_op :
      [ `Neg ] * 'a bounded integer * [ `Check | `Modulo ] ->
    ('a bounded integer number * unit, 'a bounded integer number) func
  | Of_int : 'a bounded integer * [ `Check | `Modulo ] ->
    (unbounded integer number * unit, 'a bounded integer number) func
  | To_int : 'a bounded integer -> ('a bounded integer number * unit, unbounded integer number) func
  | Any : 'a bounded integer -> (void * unit, 'a bounded integer number) func
  | Cast : 'a bounded integer * 'b bounded integer * [ `Check | `Modulo ] ->
    ('b bounded integer number * unit, 'a bounded integer number) func
  | To_float : 'a precision real -> (arbitrary_precision real number * unit, 'a precision real number) func
  | Of_float : 'a precision real -> ('a precision real number * unit, arbitrary_precision real number) func
  | B_bint_bop :
      [ `And | `Or | `Xor | `Lsr | `Asr ] * ('a repr, 'b bit) xintx bounded integer ->
    (('a repr, 'b bit) xintx bounded integer number * (('a repr, 'b bit) xintx bounded integer number * unit),
     ('a repr, 'b bit) xintx bounded integer number) func
  | U_bint_bop :
      [ `Compl ] * ('a repr, 'b bit) xintx bounded integer ->
    (('a repr, 'b bit) xintx bounded integer number * unit, ('a repr, 'b bit) xintx bounded integer number) func
  | Lsl_bint :
      ('a repr, 'b bit) xintx bounded integer * [ `Check | `Modulo ] ->
    (('a repr, 'b bit) xintx bounded integer number * (('a repr, 'b bit) xintx bounded integer number * unit),
     ('a repr, 'b bit) xintx bounded integer number) func
  | B_num_pred : [ `Lt | `Le | `Gt | `Ge | `Eq | `Ne ] * 'a number -> ('a number * ('a number * unit), boolean) func
  | Poly : [ `Eq | `Neq ] -> ('a * ('a * unit), boolean) func
  | User : (string * [ `Short | `Qualified ]) * string -> (_, _) func (** theory * use qualified name * name *)

type 'typ constant =
  | Void : void constant
  | Int : string -> unbounded integer number constant
  | Real : string -> arbitrary_precision real number constant
  | Bool : bool -> boolean constant

type 't ty =
  | Numeric : 'a number -> 'a number ty
  | Bool : boolean ty
  | Void : void ty
  | Ref : 'a ty -> 'a ref ty
  | Arrow : 'a ty * 'b ty -> ('a -> 'b) ty
  | Ex : _ ty

type ('expected, 'got) ty_opt =
  | Ty : 'expected ty -> ('expected, 'got) ty_opt
  | Any : ('got, 'got) ty_opt

type some_ty_opt = Typ : (_, _) ty_opt -> some_ty_opt

type poly_term = { term : 'a. 'a term }

and 'a term_hlist =
  | Nil : unit term_hlist
  | Cons : 'a term * 'b term_hlist -> ('a * 'b) term_hlist

and 'typ term =
  | Const : 'a constant -> 'a term
  | App : ('a, 'b) func * 'a term_hlist -> 'b term
  | Var : string -> _ term  (** immutable logic var *)
  | Deref : string -> _ term  (** [!r] *)
  | Deref_at : string * string -> _ term  (** [(at !x L)] *)
  | Typed : 'a term * 'a ty -> 'a term
  | Poly : poly_term -> _ term
  | Labeled : why_label * 'a term -> 'a term
  | If : boolean term * 'b term * 'b term -> 'b term
  | Let : string * 'a term * 'b term -> 'b term

type some_term = Term : _ term -> some_term

type ('params, 'result) tconstr =
  | Numeric : 'a number -> (unit, 'a number) tconstr
  | Bool : (unit, boolean) tconstr
  | Void : (unit, void) tconstr
  | Var : string -> (unit, 'b) tconstr
  | User : (string * [ `Short | `Qualified ]) * string -> (_, _) tconstr

type 'a ltype_hlist =
  | Nil : unit ltype_hlist
  | Cons : 'a logic_type * 'b ltype_hlist -> ('a * 'b) ltype_hlist

and 'a logic_type = Type : ('a, 'b) tconstr * 'a ltype_hlist -> 'b logic_type

type pred =
  | True | False
  | And : [`Split | `Don't_split] * pred * pred -> pred
  | Or : pred * pred -> pred
  | Iff : pred * pred -> pred
  | Not : pred -> pred
  | Impl : pred * pred -> pred
  | If : boolean term * pred * pred -> pred
  | Let : string * 'a term * pred -> pred
  | Forall : string * 'a logic_type * trigger list list * pred -> pred (** [forall x : t. a] *)
  | Exists : string * 'a logic_type * trigger list list * pred -> pred (** [exists x : t. a] *)
  | App : ('a, boolean) func * 'a term_hlist -> pred
  | Labeled : why_label * pred -> pred

and trigger =
  | Pred : pred -> trigger
  | Term : 'a term -> trigger

type poly_why_type = { why_type : 'a. 'a why_type }

and 'a why_type =
  | Arrow : string * 'a why_type * 'b why_type -> ('a -> 'b) why_type (** (x : t1) -> t2 *)
  | Logic : 'a logic_type -> 'a why_type
  | Ref : 'a why_type -> 'a ref why_type
  | Annot :
      pred * 'a why_type * string list * string list * pred *
      (((string * [ `Qualified | `Short ]) * string) * pred) list ->
    'a why_type
    (** [{ P } t reads r writes w raises E { Q | E => R }] *)
  | Typed : 'a why_type * 'a ty -> 'a why_type
  | Poly : poly_why_type -> _ why_type

type some_logic_type = Logic_type : 'a logic_type -> some_logic_type

type some_why_type = Why_type : 'a why_type -> some_why_type

type 'a variant = 'a term * string option

type assert_kind = [ `ASSERT | `CHECK | `ASSUME ]

[@@@warning "-30"]

type poly_expr_node = { expr_node : 'a. 'a expr_node }

and 'a expr_hlist =
  | Nil : unit expr_hlist
  | Cons : 'a expr * 'b expr_hlist -> ('a * 'b) expr_hlist
and 'a expr_result =
  | Void : void expr_result
  | Return : 'a expr -> 'a expr_result
and 'typ expr_node =
  | Const : 'a constant -> 'a expr_node
  | Var : string -> _ expr_node
  | And : boolean expr * boolean expr -> boolean expr_node
  | Or : boolean expr * boolean expr -> boolean expr_node
  | Not : boolean expr -> boolean expr_node
  | Void : void expr_node
  | Deref : string -> _ expr_node
  | Typed : 'a expr * 'a ty -> 'a expr_node
  | Poly : poly_expr_node -> _ expr_node
  | If : boolean expr * 'b expr * 'b expr -> 'b expr_node
  | While :
        boolean expr (** loop condition *)
      * pred (** invariant *)
      * 'a variant option (** variant *)
      * void expr list (** loop body *) ->
      void expr_node
  | Block : void expr list * 'a expr_result -> 'a expr_node
  | Assign : string * 'a expr -> void expr_node
  | Let : string * 'a expr * 'b expr -> 'b expr_node
  | Let_ref : string * 'a expr * 'b expr -> 'b expr_node
  | App : ('a, 'b) func * 'a expr_hlist * 'b why_type option -> 'b expr_node
  | Raise : ((string * [ `Qualified | `Short ]) * string) * 'a expr option -> 'b expr_node
  | Try : 'a expr * ((string * [ `Qualified | `Short ]) * string) * string option * 'a expr -> 'a expr_node
  | Fun : (string * some_why_type) list * 'b why_type * pred * 'b expr * pred *
          [ `Diverges | `Converges ] * (((string * [ `Qualified | `Short ]) * string) * pred) list ->
    'b expr_node
  (** params * result_type * pre * body * post * diverges * signals *)
  | Triple : [ `Opaque | `Transparent ] * pred * 'a expr * pred * ((string * pred) list) -> 'a expr_node
  | Assert : assert_kind * pred -> void expr_node
  | Black_box : 'a why_type -> 'a expr_node
  | Absurd : _ expr_node
  | Labeled : why_label * 'a expr -> 'a expr_node

and 'a expr = {
  expr_labels     : string list;
  expr_node       : 'a expr_node;
}

type some_expr = Expr : _ expr -> some_expr

type why_id = {
  why_name : string;
  why_expl : string;
  why_pos  : Position.t
}

type goal_kind = KAxiom | KLemma | KGoal

type 'kind decl =
  | Param : 'a why_type -> [ `Module of [ `Safe | `Unsafe ] ] decl (** parameter in why *)
  | Def : 'a expr -> [ `Module of [ `Safe | `Unsafe ] ] decl (** global let in why *)
  | Logic : (string * some_logic_type) list * 'a logic_type -> [ `Theory ] decl
    (** logic decl in why *)
  | Predicate : (string * some_logic_type) list * pred -> [ `Theory ] decl
  | Inductive : (string * some_logic_type) list * (string * pred) list -> [ `Theory ] decl
    (** inductive definition *)
  | Goal : goal_kind * pred -> [ `Theory ] decl  (** Goal *)
  | Function : (string * some_logic_type) list * 'a logic_type * 'a term -> [ `Theory ] decl
  | Type : string list -> [ `Theory ] decl
  | Exception : 'a logic_type option -> [ `Module of [ `Safe | `Unsafe ] ] decl

type 'kind why_decl = {
  why_id : why_id;
  why_decl : 'kind decl
}

type 'kind dependency =
  | Use of [ `Import of string option | `Export | `As of string option ] * 'kind entry
  | Clone of [ `Import of string option | `Export | `As of string option ] * 'kind entry *
             [ `Constant of string * string |
               `Type of string * string |
               `Function of string * string |
               `Predicate of string * string |
               `Namespace of string option * string option |
               `Lemma of string |
               `Goal of string ] list
and module_dependency = Dependency : [< `Theory | `Module of [ `Safe | `Unsafe ] ] dependency -> module_dependency
and 'kind entry =
  | Theory : why_id * ([ `Theory ] dependency list ref * [ `Theory ] why_decl list) option -> [ `Theory ] entry
  | Module :
      why_id * (module_dependency list ref *
                [ `Safe | `Unsafe ] * [ `Module of [ `Safe | `Unsafe ] ] why_decl list) option ->
    [ `Module of [ `Safe | `Unsafe ] ] entry

type some_entry = Entry : 'kind entry -> some_entry

type file = some_entry list

(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . jc_why_output_ast.mli"
  End:
*)
