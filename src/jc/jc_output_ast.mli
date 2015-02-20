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
  | JCVCdowncast
  | JCVCpointer_deref
  | JCVCpointer_deref_bounds
  | JCVCpointer_shift
  | JCVCseparation
  | JCVCindex_bounds
  | JCVCuser_call of string
  | JCVCdiv_by_zero
  | JCVCalloc_size
  | JCVCpack
  | JCVCunpack
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


type real

type enum_name = private string

type ints = [ `int8 | `uint8 | `int16 | `uint16 | `int32 | `uint32 | `int64 | `uint64 ]

type 'a bounded = [< ints | `enum of enum_name ] as 'a

type 'a integer =
  | Int8 : [`int8] integer
  | Uint8 : [`uint8] integer
  | Int16 : [`int16] integer
  | Uintnt16 : [`uint16] integer
  | Int32 : [`int32] integer
  | Uint32 : [`uint32] integer
  | Int64 : [`int64] integer
  | Uint64 : [`uint64] integer
  | Enum : enum_name -> [`enum of enum_name] integer
  | Unbounded : [`unbounded] integer
  constraint 'a = [< ints | `enum of enum_name | `unbounded ]

type 'a number =
  | Integer : 'a integer -> 'a integer number
  | Real : real number

type void

type boolean

type ('params, 'result) func =
  | B_int_op :
      [ `Add | `Sub | `Mul | `Div | `Mod ] ->
    ([`unbounded] integer number * ([`unbounded] integer number * unit), [`unbounded] integer number) func
  | U_int_op : [ `Neg ] -> ([`unbounded] integer number * unit, [`unbounded] integer number) func
  | B_bint_op :
      [ `Add | `Sub | `Mul | `Div | `Mod ] * (_ bounded as 'a) integer * bool ->
    ('a integer number * ('a integer number * unit), 'a integer number) func
  | U_bint_op :
      [ `Neg ] * (_ bounded as 'a) integer * bool -> ('a integer number * unit, 'a integer number) func
  | Of_int : (_ bounded as 'a) integer -> ([`unbounded] integer number * unit, 'a integer number) func
  | To_int : (_ bounded as 'a) integer -> ('a integer number * unit, [`unbounded] integer number) func
  | B_bint_bop :
      [`And | `Or | `Xor | `Lsr | `Asr ] * ([< ints ] as 'a) integer ->
    ('a integer number * ('a integer number * unit), 'a integer number) func
  | U_bint_bop :
    [ `Compl ] * ([< ints ] as 'a) integer -> ('a integer number * unit, 'a integer number) func
  | Lsl_bint :
      ([< ints ] as 'a) integer * bool ->
    ('a integer number * ('a integer number * unit), 'a integer number) func
  | B_num_pred : [ `Lt | `Le | `Gt | `Ge | `Eq | `Ne ] * 'a number -> ('a number * ('a number * unit), boolean) func
  | Poly : [`Eq | `Neq] -> ('a * ('a * unit), boolean) func
  | User : string * bool * string -> ('a, 'b) func (** theory * use qualified name * name *)

type 'typ constant =
  | Void : void constant
  | Int : string -> [`unbounded] integer number constant
  | Real : string -> real number constant
  | Bool : boolean constant

type 'a term_hlist =
  | Nil : unit term_hlist
  | Cons : 'a term * 'b term_hlist -> ('a * 'b) term_hlist

and 'typ term =
  | Const : 'a constant -> 'a term
  | App : ('a, 'b) func * 'a term_hlist -> 'b term
  | Var : string -> 'a term  (** immutable logic var *)
  | Deref : string -> 'a term  (** [!r] *)
  | Deref_at : string * string -> 'a term  (** [(at !x L)] *)
  | Labeled : why_label * 'a term -> 'a term
  | If : 'a term * 'b term * 'b term -> 'b term
  | Let : string * 'a term * 'b term -> 'b term

type ('params, 'result) tconstr =
  | Numeric : ('a number * unit, 'a number) tconstr
  | Bool : (unit, boolean) tconstr
  | Void : (unit, void) tconstr
  | User : string -> ('a, 'b) tconstr

type 'a ltype_hlist =
  | Nil : unit ltype_hlist
  | Cons : 'a logic_type * 'b ltype_hlist -> ('a * 'b) ltype_hlist

and 'a logic_type = Type : ('a, 'b) tconstr * 'a ltype_hlist -> 'b logic_type

type pred =
  | True | False
  | And : pred * pred -> pred
  | Or : pred * pred -> pred
  | Iff : pred * pred -> pred
  | Not : pred -> pred
  | Impl : pred * pred -> pred
  | If : 'a term * pred * pred -> pred
  | Let : string * 'a term * pred -> pred
  | Forall : string * 'a logic_type * trigger list list * pred -> pred (** [forall x : t. a] *)
  | Exists : string * 'a logic_type * trigger list list * pred -> pred (** [exists x : t. a] *)
  | App : ('a, boolean) func * 'a term_hlist -> pred
  | Labeled : why_label * pred -> pred

and trigger =
  | Pred : pred -> trigger
  | Term : 'a term -> trigger

type 'a why_type =
  | Prod_type : string * 'a why_type * 'b why_type -> ('a * 'b) why_type (** (x : t1) -> t2 *)
  | Base_type : 'a logic_type -> 'a why_type
  | Ref_type : 'a why_type -> 'a ref why_type
  | Annot_type : pred * 'a why_type * string list * string list * pred * (string * pred) list -> 'a why_type
    (** [{ P } t reads r writes w raises E { Q | E => R }] *)

type any_logic_type = Logic_type : 'a logic_type -> any_logic_type

type any_why_type = Why_type : 'a why_type -> any_why_type

type 'a variant = 'a term * string option

type opaque = bool

type assert_kind = [ `ASSERT | `CHECK | `ASSUME ]

type 'a expr_hlist =
  | Nil : unit expr_hlist
  | Cons : 'a expr * 'b expr_hlist -> ('a * 'b) expr_hlist

and 'typ expr_node =
  | Cte : 'a constant -> 'a expr_node
  | Var : string -> 'a expr_node
  | And : boolean expr * boolean expr -> boolean expr_node
  | Or : boolean expr * boolean expr -> boolean expr_node
  | Not : boolean expr -> boolean expr_node
  | Void : void expr_node
  | Deref : string -> 'a expr_node
  | If : 'a expr * 'b expr * 'b expr -> 'b expr_node
  | While :
        boolean expr (** loop condition *)
      * pred (** invariant *)
      * 'a variant option (** variant *)
      * void expr list (** loop body *) ->
      void expr_node
  | Block : void expr list -> void expr_node
  | Assign : string * 'a expr -> void expr_node
  | Let : string * 'a expr * 'b expr -> 'b expr_node
  | Let_ref : string * 'a expr * 'b expr -> 'b expr_node
  | App : ('a, 'b) func * 'a expr_hlist * 'b why_type option -> 'b expr_node
  | Raise : string * 'a expr option -> 'b expr_node
  | Try : 'a expr * string * string option * 'a expr -> 'a expr_node
  | Fun : (string * any_why_type) list * 'b why_type * pred * 'b expr * pred * bool * ((string * pred) list) ->
    'b expr_node
    (** params * result_type * pre * body * post * diverges * signals *)
  | Triple : opaque * pred * 'a expr * pred * ((string * pred) list) -> 'a expr_node
  | Assert : assert_kind * pred * boolean expr -> void expr_node
  | BlackBox : 'a why_type -> 'a expr_node
  | Absurd : void expr_node
  | Labeled : why_label * 'a expr -> 'a expr_node

and 'a expr = {
  expr_labels     : string list;
  expr_node       : 'a expr_node;
}

type why_id = {
  why_name : string;
  why_expl : string;
  why_pos  : Position.t
}

type decl_kind = [ `Theory | `Module ]

type goal_kind = KAxiom | KLemma | KGoal

type 'kind why_decl =
  | Param : bool * why_id * 'a why_type ->  [`Module] why_decl (** parameter in why *)
  | Def : why_id * 'a expr -> [`Module] why_decl (** global let in why *)
  | Logic : bool * why_id * (string * any_logic_type) list * 'a logic_type -> [`Theory] why_decl
    (** logic decl in why *)
  | Predicate : bool * why_id * (string * any_logic_type) list * pred -> [`Theory] why_decl
  | Inductive : bool * why_id * (string * any_logic_type) list * (string * pred) list -> [`Theory] why_decl
    (** inductive definition *)
  | Goal : goal_kind * why_id * pred -> [`Theory] why_decl  (** Goal *)
  | Function : bool * why_id * (string * any_logic_type) list * 'a logic_type * 'a term -> [`Theory] why_decl
  | Type : why_id * string list -> [`Theory] why_decl
  | Exception : why_id * any_logic_type option -> [`Module] why_decl

type dependency =
  | Use of [`Import | `Export | `As of string option] * entry
  | Clone of [`Import | `Export | `As of string option] * entry *
             [`Constant of string * string |
              `Type of string * string |
              `Function of string * string |
              `Predicate of string * string |
               `Namespace of string option * string option |
              `Lemma of string |
              `Goal of string] list

and entry =
  | Theory of string * (dependency list * [`Theory] why_decl list) option
  | Module of string * (dependency list * [`Module] why_decl list) option

(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . jc_why_output_ast.mli"
  End:
*)
