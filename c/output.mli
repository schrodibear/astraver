

type constant =
  | Prim_int of int
  | Prim_float of float
  | Prim_bool of bool
;;

type term = 
  | LConst of constant
  | LApp of string * term list
  | LVar of string
  | LVarAtLabel of string * string     (*r x@L *)
;;

type base_type = string list * string       (*r int, float, int list, ... *)

type assertion = 
  | LTrue | LFalse
  | LAnd of assertion * assertion
  | LOr of assertion * assertion
  | LNot of assertion
  | LImpl of assertion * assertion
  | LIf of term * assertion * assertion
  | LLet of string * term * assertion
  | LForall of string * base_type * assertion
      (*r forall x:t.a *)
  | LExists of string * base_type * assertion
      (*r exists x:t.a *)
  | LPred of string * term list
;;

val make_or : assertion -> assertion -> assertion
val make_and : assertion -> assertion -> assertion
val make_and_list : assertion list -> assertion
val make_impl : assertion -> assertion -> assertion
val make_equiv : assertion -> assertion -> assertion

val fprintf_assertion : Format.formatter -> assertion -> unit

type why_type = 
  | Prod_type of string * why_type * why_type (*r (x:t1)->t2 *)
  | Base_type of base_type
  | Ref_type of why_type
  | Annot_type of 
      assertion * why_type * 
      string list * string list * assertion * ((string * assertion) option)
	(*r { P } t reads r writes w raises E { Q | E => R } *)
;;

val int_type : why_type
val float_type : why_type
val bool_type : why_type
val unit_type : why_type
val base_type : string -> why_type

type expr =
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
      * term (* variant *) 
      * expr list (* loop body *)
  | Block of expr list
  | Assign of string * expr
  | Let of string * expr * expr
  | Let_ref of string * expr * expr
  | App of expr * expr
  | Raise of string * expr
  | Try of expr * string * string * expr
  | Fun of (string * why_type) list * 
      assertion * expr * assertion * ((string * assertion) option)
  | Triple of assertion * expr * assertion * ((string * assertion) option)
  | Assert of assertion  (*r only in blocks *)
  | Label of string
;;

(*

  [make_app id [e1;..;en])] builds
  App(...(App(Var(id),e1),...,en)

*)

val make_app : string -> expr list -> expr

(*

  [make_label l e] builds

    begin label l; e end

  applying simplification if [e] is already a block

    

*)
val make_label : string -> expr -> expr;;

(*

  [make_while cond inv dec e] builds

  while cond do { invariant inv variant dec } e

  applying simplifications if possible

*)
val make_while : expr -> assertion -> term -> expr -> expr;;



val make_pre : assertion -> expr -> expr;;

val append : expr -> expr -> expr

type why_decl =
  | Param of string * why_type         (*r parameter in why *)
  | Def of string * expr               (*r global let in why *)
  | External of string * why_type      (*r external decl in why *)
  | Logic of string * why_type         (*r logic decl in why *)
  | Axiom of string * assertion            (*r Axiom *)

type prover_decl =
  | Parameter  of string * why_type       (*r Parameter *)
  | Definition of string * expr           (*r Definition *) 
  | Predicate of string * (string * why_type) list * assertion  
                                          (*r Predicate *) 
(*
  | Axiom of string * assertion            (*r Axiom *)
*)
  | CoqVerbatim of string                 (*r Verbatim Coq text (hints...) *)


val fprintf_why_decl : Format.formatter -> why_decl -> unit;;

val fprintf_why_decls : Format.formatter -> why_decl list -> unit



