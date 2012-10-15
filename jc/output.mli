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



type constant =
  | Prim_void
  | Prim_int of string
  | Prim_real of string
  | Prim_bool of bool
(*
  | Prim_string of string
*)

type logic_type =
    { logic_type_name : string;
      logic_type_args : logic_type list;
    }

val logic_type_var : string -> logic_type

val fprintf_logic_type : Format.formatter -> logic_type -> unit


type term =
  | LConst of constant
  | LApp of string * term list
  | LVar of string                  (*r immutable logic var *)
  | LDeref of string                     (*r !r *) 
  | LDerefAtLabel of string * string     (*r x@L *)
  | Tnamed of string * term
  | TIf of term * term * term
  | TLet of string * term * term

val match_term : (string * term) list -> term -> term -> (string * term) list

val fprintf_term : Format.formatter -> term -> unit

type assertion =
  | LTrue | LFalse
  | LAnd of assertion * assertion
  | LOr of assertion * assertion
  | LIff of assertion * assertion
  | LNot of assertion
  | LImpl of assertion * assertion
  | LIf of term * assertion * assertion
  | LLet of string * term * assertion
  | LForall of string * logic_type * trigger list list * assertion
      (*r forall x:t.a *)
  | LExists of string * logic_type * trigger list list * assertion
      (*r exists x:t.a *)
  | LPred of string * term list
  | LNamed of string * assertion

and trigger =
  | LPatP of assertion
  | LPatT of term

val make_var : string -> term


val make_or : assertion -> assertion -> assertion
val make_and : assertion -> assertion -> assertion
val make_or_list : assertion list -> assertion
val make_and_list : assertion list -> assertion
val make_forall_list : (string * logic_type) list -> trigger list list
  -> assertion -> assertion
val make_impl : assertion -> assertion -> assertion
val make_impl_list : assertion -> assertion list -> assertion
val make_equiv : assertion -> assertion -> assertion

val fprintf_assertion : Format.formatter -> assertion -> unit

type why_type =
  | Prod_type of string * why_type * why_type (*r (x:t1)->t2 *)
  | Base_type of logic_type
  | Ref_type of why_type
  | Annot_type of
      assertion * why_type *
      string list * string list * assertion * ((string * assertion) list)
	(*r { P } t reads r writes w raises E { Q | E => R } *)
;;

val int_type : why_type
val bool_type : why_type
val unit_type : why_type
val base_type : string -> why_type

type variant = term * string option

type opaque = bool

type assert_kind = [`ASSERT | `CHECK]

type expr_node =
  | Cte of constant
  | Var of string
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Void
  | Deref of string
  | If of expr * expr * expr
  | While of
      expr (* loop condition *)
      * assertion (* invariant *)
      * variant option (* variant *)
      * expr list (* loop body *)
  | Block of expr list
  | Assign of string * expr
  | MultiAssign of string * Loc.position * (string * expr) list *
      bool * term * expr * string * expr * string *
      (int * bool * bool * string) list
      (*

         this construction is not in Why, but a temporary construction
         used by jessie to denote "parallel updates"

         [MultiAssign(mark,pos,lets,talloc,alloc,tmpe,e,f,l)] where [l]
         is a list of pair (i,b1,b2,e') for distincts i, denotes the
         parallel updates (lets) let tmpe = e in (tmpe+i).f = e'

         booleans [b1] and [b2] indicates whether it is safe to ignore
         bound checking on the left resp on the right

         [alloc] is the allocation table for safety conditions
         [lets] is a sequence of local bindings for expressions e'
      *)
  | Let of string * expr * expr
  | Let_ref of string * expr * expr
  | App of expr * expr * why_type option
  | Raise of string * expr option
  | Try of expr * string * string option * expr
  | Fun of (string * why_type) list *
      assertion * expr * assertion * ((string * assertion) list)
  | Triple of opaque *
      assertion * expr * assertion * ((string * assertion) list)
  | Assert of assert_kind * assertion * expr
(*
  | Label of string * expr
*)
  | BlackBox of why_type
  | Absurd
  | Loc of Lexing.position * expr

and expr =
    { expr_labels : string list;
      expr_node : expr_node;
    }

;;

val mk_expr : expr_node -> expr
val mk_var : string -> expr
val void : expr

val make_block : string list -> expr list -> expr

val fprintf_expr : Format.formatter -> expr -> unit

val make_or_expr : expr -> expr -> expr
val make_and_expr : expr -> expr -> expr


(*

  [make_app id [e1;..;en])] builds
  App(...(App(Var(id),e1),...,en)

*)

val make_app : ?ty:why_type -> string -> expr list -> expr
val make_logic_app : ?ty:why_type -> string -> expr list -> expr
val make_app_e : ?ty:why_type -> expr -> expr list -> expr

(*

  [make_label l e] adds label l to e

  In the case of a block, add it to the first instruction of the block, if there
  is one.
*)

val make_label : string -> expr -> expr;;

(*

  [make_while cond inv dec e] builds

  while cond do { invariant inv variant dec } e

  applying simplifications if possible

*)
val make_while : expr -> assertion -> variant option -> expr -> expr;;

val make_pre : assertion -> expr -> expr;;

val append : expr -> expr -> expr

type why_id = { name : string ; loc : Loc.floc }

val id_no_loc : string -> why_id

type goal_kind = KAxiom | KLemma | KGoal

type why_decl =
  | Param of bool * why_id * why_type         (*r parameter in why *)
  | Def of why_id * expr               (*r global let in why *)
  | Logic of bool * why_id * (string * logic_type) list * logic_type    (*r logic decl in why *)
  | Predicate of bool * why_id * (string * logic_type) list * assertion
  | Inductive of bool * why_id * (string * logic_type) list *
      (string * assertion) list (*r inductive definition *)
  | Goal of goal_kind * why_id * assertion         (*r Goal *)
  | Function of bool * why_id * (string * logic_type) list * logic_type * term
  | Type of why_id * string list
  | Exception of why_id * logic_type option

val fprintf_why_decl : Format.formatter -> why_decl -> unit;;

val fprintf_why_decls : ?why3:bool -> ?use_floats:bool -> 
  float_model:Jc_env.float_model -> Format.formatter -> why_decl list -> unit

type kind =
  | VarDecr
  | ArithOverflow
  | DownCast
  | IndexBounds
  | PointerDeref
  | UserCall
  | DivByZero
  | AllocSize
  | Pack
  | Unpack
  | FPoverflow

val print_kind : Format.formatter -> kind -> unit

(*
val pos_table :
    (string, (kind option * string option * string option *
                string * int * int * int))
    Hashtbl.t
*)

(*
val my_pos_table :
    (string, (kind option * string option * string option *
                string * int * int * int))
    Hashtbl.t
*)

val my_add_pos :
  string -> (kind option * string option * string option *
               string * int * int * int) -> unit

val my_print_locs : Format.formatter -> unit

(* backward compatibility for Krakatoa and Jessie plugin *)

val old_reg_pos : string -> ?id:string -> ?kind:kind -> ?name:string
  -> ?formula:string -> Loc.floc -> string

val old_print_pos : Format.formatter -> unit


