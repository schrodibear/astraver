
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: types.mli,v 1.3 2001-08-19 02:44:48 filliatr Exp $ *)

open Logic

(*s Pre- and postconditions. *)

type precondition = 
  { p_assert : bool; 
    p_name : Ident.name; 
    p_value : predicate }

type assertion  = { a_name : Ident.name; a_value : predicate }

type postcondition = assertion

(*s Binders. *)

type 'a binder_type =
  | BindType of 'a
  | BindSet
  | Untyped

type 'a binder = Ident.t * 'a binder_type

(*s Pure types. *)

type pure_type =
  | PTint
  | PTbool
  | PTfloat
  | PTunit
  | PTexternal of Ident.t

(*s Variant. *)

type variant = term * term * pure_type (* phi, R, A *)

(*s Types of values... *)

type type_v =
  | Ref       of type_v
  | Array     of term * type_v   (* size x type *)
  | Arrow     of type_v binder list * type_c
  | PureType  of pure_type

(* ... and types of computations. 
 *
 * INVARIANT: l'effet E contient toutes les variables apparaissant dans
 *            le programme ET les annotations P et Q
 *            Si E = { x1,...,xn | y1,...,ym }, les variables x sont les
 *            variables en lecture seule et y1 les variables modifiées
 *            les xi sont libres dans P et Q, et les yi,result liées dans Q
 *            i.e.  P = p(x)
 *               et Q = [y1]...[yn][res]q(x,y,res)
 *)

and type_c =
  { c_result_name : Ident.t;
    c_result_type : type_v;
    c_effect : Effect.t;
    c_pre    : precondition list;
    c_post   : postcondition option }
